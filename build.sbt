scalaVersion in ThisBuild := "2.12.1"
crossScalaVersions in ThisBuild := Seq("2.11.8", "2.12.1")

import ReleaseTransformations._

releaseProcess := Seq[ReleaseStep](
  checkSnapshotDependencies,
  inquireVersions,
  runClean,
  runTest,
  setReleaseVersion,
  commitReleaseVersion,
  tagRelease,
  ReleaseStep(action = Command.process("publishSigned", _)),
  setNextVersion,
  commitNextVersion,
  ReleaseStep(action = Command.process("sonatypeReleaseAll", _)),
  pushChanges
)

val gf = crossProject.in(file("."))
    .settings(
        name := "Scala GF",
        normalizedName := "scala-gf",
        libraryDependencies ++= Seq(
            "com.lihaoyi" %%% "fastparse-byte" % "0.4.2",
            "org.scalaz" %%% "scalaz-core" % "7.2.7",
            "org.scalatest" %% "scalatest" % "3.0.0" % "test"
        ),
        scalaJSStage in Global := FullOptStage,
        organization := "eu.tilk",
        version := "0.0.1-SNAPSHOT",
        licenses += ("LGPL 3.0", url("https://opensource.org/licenses/LGPL-3.0")),
        scmInfo := Some(ScmInfo(
            url("https://github.com/tilk/scala-gf"),
            "scm:git:git@github.com:tilk/scala-gf.git",
            Some("scm:git:git@github.com:tilk/scala-gf.git"))),
        publishTo := {
          val nexus = "https://oss.sonatype.org/"
          if (isSnapshot.value)
            Some("snapshots" at nexus + "content/repositories/snapshots")
          else
            Some("releases" at nexus + "service/local/staging/deploy/maven2")
        },
        publishMavenStyle := true,
        pomExtra := (
          <developers>
            <developer>
              <id>tilk</id>
              <name>Marek Materzok</name>
              <url>https://github.com/tilk/</url>
            </developer>
          </developers>
        )
    )
    .jvmSettings(
        name := "Scala GF JVM"
    )
    .jsSettings(
        name := "Scala GF JS"
    )

lazy val gfJS = gf.js
lazy val gfJVM = gf.jvm

