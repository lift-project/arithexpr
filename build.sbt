name := "ArithExpr"

version := "1.0"

scalaVersion := "2.11.8"

scalacOptions ++= Seq("-Xmax-classfile-name", "100", "-unchecked", "-deprecation", "-feature")

scalaSource in Compile <<= baseDirectory(_ / "src/main")

scalaSource in Test <<= baseDirectory(_ / "src/test")

javaSource in Compile <<= baseDirectory(_ / "src/main")

javaSource in Test <<= baseDirectory(_ / "src/test")

libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.11.8"

libraryDependencies += "org.scala-lang" % "scala-compiler" % "2.11.8"

libraryDependencies += "org.scala-lang" % "scala-library" % "2.11.8"

libraryDependencies += "org.scala-lang.modules" % "scala-xml_2.11" % "1.0.4"

libraryDependencies += "junit" % "junit" % "4.11"

libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.13.0" % "test"

libraryDependencies += "com.novocode" % "junit-interface" % "0.11" % "test"

libraryDependencies += "org.clapper" %% "argot" % "1.0.3"

scalacOptions in (Compile,doc) := Seq("-implicits", "-diagrams")

testOptions += Tests.Argument(TestFrameworks.JUnit, "-q", "-v")

testOptions += Tests.Argument(TestFrameworks.ScalaCheck, "-verbosity", "5")

ScoverageSbtPlugin.ScoverageKeys.coverageExcludedPackages := "<empty>;.*Test.*;.*testing.*"

fork := true
