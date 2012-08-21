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
import java.io.ByteArrayOutputStream
import java.io.PrintWriter

// TODO why do I need GlobalIndexes?
abstract class ForComprehensionTransformBinding extends MultiStageRefactoring with GlobalIndexes with HasLogger with PimpedTrees {
      
  this: common.CompilerAccess =>
  
  import global._
  import global.definitions._
  
  case class PreparationResult(appNode:Tree, generatorString: String, yieldBodyString: String)  
  
  class RefactoringParameters
  
  val forComprehensionString = "for (%s) yield %s"
    
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
		          case None =>
		            eclipseLog.warn("case Apply isInnerMap - select not found")
		            None
		        }
		      case Apply(fun, List(Function(List(vparam), body))) if isFlatMap(fun) =>
		        val traverser = new FindTreeTraverser( (_:Tree).isInstanceOf[Select] )
		        traverser.traverse(fun)
		        traverser.result match {
		          case Some(selectTree) =>
		          	extractIfTranfsormableRec(body, flatMaps :+ GeneratorInfo(variable = vparam, generator = selectTree))
		          case None => 
		            eclipseLog.warn("case Apply isFlatMap - select not found")
		            None
		        }
		      case Apply(fun, args) =>
            eclipseLog.warn("case _, fun.symbol.nameString = " + fun.symbol.nameString)
            eclipseLog.warn("args.size = " + args.size)
            eclipseLog.warn("traverse args.head: " + typeTreeTraverser(args.head))
            eclipseLog.warn("isInnerMap(fun) = " + isInnerMap(fun))
            args.head match {
              case Function(params, body) =>
              	eclipseLog.warn("args.head match Function, params.size" + params.size)
              case w =>
              	eclipseLog.warn("args.head doenst match Function, it matches: " + determineType(w))
            }
            None
		      case _ => 
            eclipseLog.warn("case _, determine type = " + determineType(treeToCheck))
            None
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
      eclipseLog.info("isFlatMap(applyNode)" + isFlatMap(applyNode))
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
          eclipseLog.info("extract failed: ")
          printTree(applyNode)
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
        
        Right(PreparationResult(applyNode, paramName + """ <- """ + generatorChars.mkString, yieldBodyChars.mkString))
      } else failure
    }
        
    res getOrElse failure
    
//    failure
  }
  
  def perform(selection: Selection, preparationResult: PreparationResult, params: RefactoringParameters): Either[RefactoringError, List[Change]] = {

    val PreparationResult(appNode, generator, yieldBody)   = preparationResult
            
    eclipseLog.info("replace with: " + forComprehensionString.format(generator, yieldBody))  
        
    val replacement = {
      PlainText.Indented(
        forComprehensionString.format(generator, yieldBody)
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
  
  
  // helpers
  def determineType(tree: Tree): String = {
      tree match {
        case DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
          ("tree: " + "DefDef")
        case TypeDef(mods, name, tparams, rhs) =>
          ("tree: " + "TypeDef")

        case LabelDef(name, params, rhs) =>
          ("tree: " + "LabelDef")

        case imp @ Import(expr, selectors) =>
          ("tree: " + "@ Import")

        case Block(stats, expr) =>
          ("tree: " + "Block")
        case CaseDef(pat, guard, body) =>
          ("tree: " + "CaseDef")
        case Alternative(trees) =>
          ("tree: " + "Alternative")
        case Star(elem) =>
          ("tree: " + "Star")
        case Bind(name, body) =>
          ("tree: " + "Bind")
        case UnApply(fun, args) =>
          ("tree: " + "UnApply")
        case ArrayValue(elemtpt, trees) =>
          ("tree: " + "ArrayValue")
        case Function(vparams, body) =>
          ("tree: " + "Function")
        case Assign(lhs, rhs) =>
          ("tree: " + "Assign")
        case If(cond, thenp, elsep) =>
          ("tree: " + "If")
        case Match(selector, cases) =>
          ("tree: " + "Match")
        case Return(expr) =>
          ("tree: " + "Return")
        case Try(block, catches, finalizer) =>
          ("tree: " + "Try")
        case Throw(expr) =>
          ("tree: " + "Throw")
        case New(tpt) =>
          ("tree: " + "New")
        case Typed(expr, tpt) =>
          ("tree: " + "Typed")
        case TypeApply(fun, args) =>
          ("tree: " + "TypeApply")
        case Apply(fun, args) =>
          ("tree: " + "Apply")
        case ApplyDynamic(qual, args) =>
          ("tree: " + "ApplyDynamic")
        case Select(qualifier, selector) =>
          ("tree: " + "Select")
        case SingletonTypeTree(ref) =>
          ("tree: " + "SingletonTypeTree")
        case SelectFromTypeTree(qualifier, selector) =>
          ("tree: " + "SelectFromTypeTree")
        case CompoundTypeTree(templ) =>
          ("tree: " + "CompoundTypeTree")
        case AppliedTypeTree(tpt, args) =>
          ("tree: " + "AppliedTypeTree")
        case TypeBoundsTree(lo, hi) =>
          ("tree: " + "TypeBoundsTree")
        case ExistentialTypeTree(tpt, whereClauses) =>
          ("tree: " + "ExistentialTypeTree")
        case SelectFromArray(qualifier, selector, erasure) =>
          ("tree: " + "SelectFromArray")

        case _ => ("no type?!")
      }
    }
  
  def typeTreeTraverser = new ForeachTreeTraverser(x => eclipseLog.info(determineType(x)))
  def printTree(tree: Tree) = {
    val byteArrayOutputStream = new ByteArrayOutputStream
    val pw = new PrintWriter(byteArrayOutputStream)
    newTreePrinter(pw).print(tree)
    pw.flush()
    byteArrayOutputStream.toString
  }
}
