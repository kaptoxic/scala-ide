package scala.tools.eclipse.lexical

import scala.xml.Elem
import org.eclipse.jface.text.IDocument
import org.junit.Assert._
import org.junit.{ Test, Before }

import scala.tools.eclipse.lexical.ScalaPartitions._
import org.eclipse.jface.text.IDocument.DEFAULT_CONTENT_TYPE
import org.eclipse.jdt.ui.text.IJavaPartitions._

class ScalaPartitionTokeniserTest {
  import ScalaPartitionTokeniserTest._

  @Test
  def bug2522 {
    // 000000000011111111112222222222333333333344444444445
    // 012345678901234567890123456789012345678901234567890 
    """def dev = <div class="menu">...</div>""" ==>
      ((DEFAULT_CONTENT_TYPE, 0, 9), (XML_TAG, 10, 27), (XML_PCDATA, 28, 30), (XML_TAG, 31, 36))
  }

  @Test
  def defaultContent {
    // 000000000011111111112222222222333333333344444444445
    // 012345678901234567890123456789012345678901234567890 
    """package foo""" ==> ((DEFAULT_CONTENT_TYPE, 0, 10))
  }

  @Test
  def comments {
    // 000000000011111111112222222222333333333344444444445
    // 012345678901234567890123456789012345678901234567890 
    """package /* comment */ foo // comment""" ==>
      ((DEFAULT_CONTENT_TYPE, 0, 7), (JAVA_MULTI_LINE_COMMENT, 8, 20), (DEFAULT_CONTENT_TYPE, 21, 25), (JAVA_SINGLE_LINE_COMMENT, 26, 35))

    // 000000000011111111112222222222333333333344444444445
    // 012345678901234567890123456789012345678901234567890 
    """/* comment /* nested */ */""" ==>
      ((JAVA_MULTI_LINE_COMMENT, 0, 25))

    // 000000000011111111112222222222333333333344444444445
    // 012345678901234567890123456789012345678901234567890 
    """/** comment /** nested **/ */""" ==>
      ((JAVA_DOC, 0, 28))

  }

  @Test
  def basicXml {
    // 000000000011111111112222222222333333333344444444445
    // 012345678901234567890123456789012345678901234567890 
    """<foo/>""" ==> ((XML_TAG, 0, 5))

    // 000000000011111111112222222222333333333344444444445
    // 012345678901234567890123456789012345678901234567890 
    """<![CDATA[ <foo/> ]]>""" ==> ((XML_CDATA, 0, 19))

    // 000000000011111111112222222222333333333344444444445
    // 012345678901234567890123456789012345678901234567890 
    """<!-- comment -->""" ==> ((XML_COMMENT, 0, 15))

    // 000000000011111111112222222222333333333344444444445
    // 012345678901234567890123456789012345678901234567890 
    """<?xml version='1.0' encoding='UTF-8'?>""" ==> ((XML_PI, 0, 37))
  }

  @Test
  def strings {
    // 000000000011111111112222222222333333333344444444445
    // 012345678901234567890123456789012345678901234567890 
    <t>"ordinary string"</t> ==> ((JAVA_STRING, 0, 16));

    // 000000000011111111112222222222333333333344444444445
    // 012345678901234567890123456789012345678901234567890 
    <t>"""scala multiline string"""</t> ==> ((SCALA_MULTI_LINE_STRING, 0, 27))
  }

  @Test
  def stringInterpolation {
    // 000000000011111111112222222222333333333344444444445
    // 012345678901234567890123456789012345678901234567890 
    <t>s"my name is $name"</t> ==>
      ((DEFAULT_CONTENT_TYPE, 0, 0), (JAVA_STRING, 1, 13), (DEFAULT_CONTENT_TYPE, 14, 17), (JAVA_STRING, 18, 18))

    // 000000000011111111112222222222333333333344444444445
    // 012345678901234567890123456789012345678901234567890 
    <t>s"""my name is $name"""</t> ==>
      ((DEFAULT_CONTENT_TYPE, 0, 0), (SCALA_MULTI_LINE_STRING, 1, 15), (DEFAULT_CONTENT_TYPE, 16, 19), (SCALA_MULTI_LINE_STRING, 20, 22))

    // 000000000011111111112222222222333333333344444444445
    // 012345678901234567890123456789012345678901234567890 
    """s"my name is ${person.name}"""" ==>
      ((DEFAULT_CONTENT_TYPE, 0, 0), (JAVA_STRING, 1, 13), (DEFAULT_CONTENT_TYPE, 14, 26), (JAVA_STRING, 27, 27))

    // 0 0 00000001111111111222222222 2 3 33333333344444444445
    // 1 2 34567890123456789012345678 9 0 12345678901234567890 
    "s\"\"\"my name is ${person.name}\"\"\"" ==>
      ((DEFAULT_CONTENT_TYPE, 0, 0), (SCALA_MULTI_LINE_STRING, 1, 15), (DEFAULT_CONTENT_TYPE, 16, 28), (SCALA_MULTI_LINE_STRING, 29, 31))

  }

}

object ScalaPartitionTokeniserTest {
  implicit def string2PimpedString(from: String): PimpedString = new PimpedString(from)
  implicit def element2PimpedString(from: Elem): PimpedString = new PimpedString(from.text)

  class PimpedString(source: String) {
    def ==>(expectedPartitions: List[(String, Int, Int)]) {
      val actualPartitions = ScalaPartitionTokeniser.tokenise(source)
      assertEquals(source, expectedPartitions map ScalaPartitionRegion.tupled toList, actualPartitions)
    }
    def ==>(expectedPartitions: (String, Int, Int)*) { this ==> expectedPartitions.toList }
  }

  def partitions(expectedPartitions: (String, Int, Int)*) = expectedPartitions.toList

}