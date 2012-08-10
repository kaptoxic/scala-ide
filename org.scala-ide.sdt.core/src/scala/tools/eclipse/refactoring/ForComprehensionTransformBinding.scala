package scala.tools.refactoring

import common.Change
import tools.nsc.symtab.Flags
import transformation.TreeFactory
import scala.tools.refactoring.analysis.GlobalIndexes
import scala.tools.eclipse.logging.HasLogger
import scala.tools.refactoring.common.PimpedTrees

// TODO why do I need GlobalIndexes?
abstract class ForComprehensionTransformBinding extends MultiStageRefactoring with GlobalIndexes with HasLogger with PimpedTrees {
      
  this: common.CompilerAccess =>
  
  import global._
  
  case class PreparationResult(appNode:Tree, valueDef: String, generatorString: String, yieldBodyString: String)  
  
  class RefactoringParameters
  
  val forComprehensionString = "for (%s <- %s) yield %s"
  
  def prepare(s: Selection): Either[PreparationError, PreparationResult] = {
    eclipseLog.info("ForComprehensionTransformBinding prepare called.")
    
    // prepare failure response
    def failure = Left(PreparationError("No appropriate for comprehension transformable expressions found."))

    def determineType(tree: Tree) {
      tree match {
        case DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
          eclipseLog.info("tree: " + "DefDef")
        case TypeDef(mods, name, tparams, rhs) =>
          eclipseLog.info("tree: " + "TypeDef")

        case LabelDef(name, params, rhs) =>
          eclipseLog.info("tree: " + "LabelDef")

        case imp @ Import(expr, selectors) =>
          eclipseLog.info("tree: " + "@ Import")

        case Block(stats, expr) =>
          eclipseLog.info("tree: " + "Block")
        case CaseDef(pat, guard, body) =>
          eclipseLog.info("tree: " + "CaseDef")
        case Alternative(trees) =>
          eclipseLog.info("tree: " + "Alternative")
        case Star(elem) =>
          eclipseLog.info("tree: " + "Star")
        case Bind(name, body) =>
          eclipseLog.info("tree: " + "Bind")
        case UnApply(fun, args) =>
          eclipseLog.info("tree: " + "UnApply")
        case ArrayValue(elemtpt, trees) =>
          eclipseLog.info("tree: " + "ArrayValue")
        case Function(vparams, body) =>
          eclipseLog.info("tree: " + "Function")
        case Assign(lhs, rhs) =>
          eclipseLog.info("tree: " + "Assign")
        case If(cond, thenp, elsep) =>
          eclipseLog.info("tree: " + "If")
        case Match(selector, cases) =>
          eclipseLog.info("tree: " + "Match")
        case Return(expr) =>
          eclipseLog.info("tree: " + "Return")
        case Try(block, catches, finalizer) =>
          eclipseLog.info("tree: " + "Try")
        case Throw(expr) =>
          eclipseLog.info("tree: " + "Throw")
        case New(tpt) =>
          eclipseLog.info("tree: " + "New")
        case Typed(expr, tpt) =>
          eclipseLog.info("tree: " + "Typed")
        case TypeApply(fun, args) =>
          eclipseLog.info("tree: " + "TypeApply")
        case Apply(fun, args) =>
          eclipseLog.info("tree: " + "Apply")
        case ApplyDynamic(qual, args) =>
          eclipseLog.info("tree: " + "ApplyDynamic")
        case Select(qualifier, selector) =>
          eclipseLog.info("tree: " + "Select")
        case SingletonTypeTree(ref) =>
          eclipseLog.info("tree: " + "SingletonTypeTree")
        case SelectFromTypeTree(qualifier, selector) =>
          eclipseLog.info("tree: " + "SelectFromTypeTree")
        case CompoundTypeTree(templ) =>
          eclipseLog.info("tree: " + "CompoundTypeTree")
        case AppliedTypeTree(tpt, args) =>
          eclipseLog.info("tree: " + "AppliedTypeTree")
        case TypeBoundsTree(lo, hi) =>
          eclipseLog.info("tree: " + "TypeBoundsTree")
        case ExistentialTypeTree(tpt, whereClauses) =>
          eclipseLog.info("tree: " + "ExistentialTypeTree")
        case SelectFromArray(qualifier, selector, erasure) =>
          eclipseLog.info("tree: " + "SelectFromArray")

        case _ => eclipseLog.info("no type?!")
      }
    }
    def fullName(sym: Symbol) = "method " + sym.fullName + sym.tpe.paramTypes.map(x => x.typeSymbol.fullName).mkString(" ", ",", "")

    def checkIfFunctionType(tpe: Type): Boolean = {
      def getApplicationInfoMethodRec(methodType: Type): Boolean = methodType match {
        case MethodType(params, resultType) => true
        case t => false
      }

      def getApplicationInfoFunctionRec(functionType: Type): Boolean = functionType match {
        case TypeRef(pre: Type, sym: Symbol, args: List[Type]) if (definitions.isFunctionType(functionType)) || (definitions.isFunctionType(pre)) =>
          true
        case t => false
      }

      val result = getApplicationInfoMethodRec(tpe) || getApplicationInfoFunctionRec(tpe)
      result
    }
    
    def isTransformable(functionNode: Tree) = functionNode.tpe match {
      case MethodType(params, resultType) if "map" == functionNode.symbol.nameString && params.size == 1 =>
        true
      case tr@TypeRef(pre: Type, sym: Symbol, args: List[Type]) if (definitions.isFunctionType(tr)) 
    	&& "map" == functionNode.symbol.nameString && args.size == 1 =>
       true
      case _ => false
    }
    
    // find Apply tree nodes
    val res = for (applyNode@Apply(fun, args) <- s.findSelectedOfType[Apply]) yield {

      /* deal with map defined as method */
      
      // check if applied function term is suitable for transformation
      if (isTransformable(fun)) {
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
  }
  
  def perform(selection: Selection, preparationResult: PreparationResult, params: RefactoringParameters): Either[RefactoringError, List[Change]] = {

    val PreparationResult(appNode, valueDef, generator, yieldBody)   = preparationResult
            
    eclipseLog.info("replace with: " + forComprehensionString.format(valueDef, generator, yieldBody))  
        
    val replacement = {
//      PlainText.Indented(
//        forComprehensionString.format(valueDef, generator, yieldBody)
//  		)
            
      appNode
  		PlainText.Indented("""
               |for (
               |  i <- list
               |) yield {
               |  i * 2
               |}""".stripMargin)
    } replaces appNode
    
    Right(refactor(List(replacement)))
  }
  
  def index: IndexLookup = sys.error("")
  
}
