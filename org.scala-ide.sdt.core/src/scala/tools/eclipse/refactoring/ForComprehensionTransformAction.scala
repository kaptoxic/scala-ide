/*
 * Copyright 2005-2010 LAMP/EPFL
 */

package scala.tools.eclipse.refactoring

import scala.tools.eclipse.javaelements.ScalaSourceFile
import scala.tools.refactoring.ForComprehensionTransformBinding

/**
 * TODO Ivan update comments
 */
class ForComprehensionTransformAction extends RefactoringAction with ActionWithNoWizard {

  def createRefactoring(selectionStart: Int, selectionEnd: Int, file: ScalaSourceFile) =
    new ForComprehensionTransformScalaIdeRefactoring(selectionStart, selectionEnd, file)

  class ForComprehensionTransformScalaIdeRefactoring(start: Int, end: Int, file: ScalaSourceFile)
    extends ScalaIdeRefactoring("For comprehension transform", file, start, end) {

    val refactoring = file.withSourceFile((sourceFile, compiler) => new ForComprehensionTransformBinding {
      val global = compiler
    })()

    /**
     * The refactoring does not take any parameters.
     */
    def refactoringParameters = new refactoring.RefactoringParameters
  }
}
