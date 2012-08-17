package scala.tools.refactoring

import common.Change
import tools.nsc.symtab.Flags
import transformation.TreeFactory
import scala.tools.refactoring.analysis.GlobalIndexes
import scala.tools.eclipse.logging.HasLogger
import scala.tools.refactoring.common.PimpedTrees
import sourcegen.SourceGenerator
import common.{SilentTracing, ConsoleTracing, Change}
import tools.nsc.symtab.Flags
import tools.nsc.ast.parser.Tokens
import scala.tools.nsc.ast.Trees

// TODO why do I need GlobalIndexes?
abstract class ForComprehensionTransformBinding extends MultiStageRefactoring with GlobalIndexes with HasLogger with PimpedTrees {
      
  this: common.CompilerAccess =>
  
  import global._
  import global.definitions._
  
  case class PreparationResult(appNode:Tree, valueDef: String, generatorString: String, yieldBodyString: String)  
  
  class RefactoringParameters
  
  val forComprehensionString = "for (%s <- %s) yield %s"
    
  trait ForComprehensionInfo
    
  case class GeneratorInfo(variable: Tree, generator: Tree) extends ForComprehensionInfo
  
  def prepare(s: Selection): Either[PreparationError, PreparationResult] = {
    eclipseLog.info("ForComprehensionTransformBinding prepare called.")
    
    // prepare failure response
    def failure = Left(PreparationError("No appropriate for comprehension transformable expressions found."))
    
    def isTransformable(tree: Tree): Boolean = tree match {
      case Apply(fun, args) if isInnerMap(fun) => true
      case Apply(fun, List(Function(vparams, body))) if isFlatMap(fun) => isTransformable(body)
      case _ => false
    }
    
    def extractIfTransformable(tree: Tree):
    	Option[(List[GeneratorInfo], Tree)] = {
      
      def extractIfTranfsormableRec(treeToCheck: Tree, flatMaps: List[GeneratorInfo]):
    	Option[(List[GeneratorInfo], Tree)] =      
			  treeToCheck match {
		      case Apply(fun, List(Function(List(vparam), body))) if isInnerMap(fun) =>
		        val traverser = new FindTreeTraverser( (_:Tree).isInstanceOf[Select] )
		        traverser.traverse(fun)
		        traverser.result match {
		          case Some(selectTree@Select(generator, _)) =>
		          	Some( (flatMaps :+ GeneratorInfo(variable = vparam, generator = selectTree), generator) )
		          case None => None
		        }
		      case Apply(fun, List(Function(List(vparam), body))) if isFlatMap(fun) =>
		        val traverser = new FindTreeTraverser( (_:Tree).isInstanceOf[Select] )
		        traverser.traverse(fun)
		        traverser.result match {
		          case Some(selectTree) =>
		          	extractIfTranfsormableRec(body, flatMaps :+ GeneratorInfo(variable = vparam, generator = selectTree))
		          case None => None
		        }
		      case _ => None
		    }
      
      extractIfTranfsormableRec(tree, List.empty)
    }
    
    // TODO check types
    def isFlatMap(functionNode: Tree) = functionNode.tpe match {
      case MethodType(params, resultType) if "flatMap" == functionNode.symbol.nameString && params.size == 1 =>
        true
      case tr@TypeRef(pre: Type, sym: Symbol, args: List[Type]) if (definitions.isFunctionType(tr)) 
    	&& "flatMap" == functionNode.symbol.nameString && args.size == 1 =>
       true
      case _ => false
    }
    
    def isInnerMap(functionNode: Tree) = functionNode.tpe match {
      case MethodType(params, resultType) if "map" == functionNode.symbol.nameString && params.size == 1 =>
        true
      case tr@TypeRef(pre: Type, sym: Symbol, args: List[Type]) if (definitions.isFunctionType(tr)) 
    	&& "map" == functionNode.symbol.nameString && args.size == 1 =>
       true
      case _ => false
    }
       
    val sourceContent = s.root.pos.source.content
    
    def treeString(tree: Tree) = tree match {
      case v:ValDef => v.nameString
      case _ => 
        val arrayToStoreChars = Array.ofDim[Char](tree.pos.end - tree.pos.start)
        System.arraycopy(sourceContent, tree.pos.start, arrayToStoreChars, 0, tree.pos.end - tree.pos.start)
        arrayToStoreChars.mkString
    }
    
    def getSourceString(info: ForComprehensionInfo) = {          
	    info match {  	      
			  case GeneratorInfo(variable, generator) =>
			    treeString(variable) + """<-""" + treeString(generator)  			     
	    }
  	}	
    
    
    for (applyNode@Apply(fun, args) <- s.findSelectedOfType[Apply]) {
      eclipseLog.info("isTransformable(applyNode)" + isTransformable(applyNode))
    }    
    
    for (applyNode@Apply(fun, args) <- s.findSelectedOfType[Apply]) {
      eclipseLog.info("extractIfTransformable(applyNode)" + extractIfTransformable(applyNode))
    }
    
    for (applyNode@Apply(fun, args) <- s.findSelectedOfType[Apply]) {
      extractIfTransformable(applyNode) match {
        case (Some((listOfGenerators, body))) => 
          val string = "for (" + listOfGenerators.map( info => getSourceString(info)).mkString(";") + ") yield {" +
          	treeString(body) + "}"
        	eclipseLog.info("string: " + string)
        case None =>
      }
    }
    
    // find Apply tree nodes
    val res = for (applyNode@Apply(fun, args) <- s.findSelectedOfType[Apply]) yield {

      /* deal with map defined as method */
      
      // check if applied function term is suitable for transformation
      if (isInnerMap(fun)) {
        // extract yield body
        val (paramName, body) = args.head match {
          case Function(List(vparam), body) =>
            // get parameter name (String) that body uses
            val paramName = vparam.nameString
            (paramName, body)
        }
        eclipseLog.info("(paramName, body): " + (paramName, body))        
                
        val yieldBodyChars = Array.ofDim[Char](body.pos.end - body.pos.start)
        System.arraycopy(body.pos.source.content, body.pos.start, yieldBodyChars, 0, body.pos.end - body.pos.start)

        eclipseLog.info("yieldBodyString: " + yieldBodyChars.mkString)

        // extract generator
        val Select(generator, _) = s.findSelectedOfType[Select].get
        
        val generatorChars = Array.ofDim[Char](generator.pos.end - generator.pos.start)
        System.arraycopy(generator.pos.source.content, generator.pos.start, generatorChars, 0, generator.pos.end - generator.pos.start)

        eclipseLog.info("generatorString: " + generatorChars.mkString)
        
        Right(PreparationResult(applyNode, paramName, generatorChars.mkString, yieldBodyChars.mkString))
      } else failure
    }
        
    res getOrElse failure
    
//    failure
  }
  
  def perform(selection: Selection, preparationResult: PreparationResult, params: RefactoringParameters): Either[RefactoringError, List[Change]] = {

    val PreparationResult(appNode, valueDef, generator, yieldBody)   = preparationResult
            
    eclipseLog.info("replace with: " + forComprehensionString.format(valueDef, generator, yieldBody))  
        
    val replacement = {
      PlainText.Indented(
        forComprehensionString.format(valueDef, generator, yieldBody)
  		)
            
//      appNode
//  		PlainText.Indented("""
//               |for (
//               |  i <- list
//               |) yield {
//               |  i * 2
//               |}""".stripMargin)
    } replaces appNode
    
    Right(refactor(List(replacement)))
  }
  
  def index: IndexLookup = sys.error("")
  
}
