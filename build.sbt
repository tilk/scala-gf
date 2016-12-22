scalaVersion in ThisBuild := "2.11.8"

val gf = crossProject.in(file("."))
    .settings(
        name := "Scala GF",
        normalizedName := "scala-gf",
        libraryDependencies ++= Seq(
            "com.lihaoyi" %%% "fastparse-byte" % "0.4.1",
            "org.scalaz" %%% "scalaz-core" % "7.2.7",
            "org.scalatest" %% "scalatest" % "3.0.0" % "test"
        ),
        scalaJSStage in Global := FullOptStage,
        organization := "eu.tilk",
        version := "0.0.1",
        scalaVersion := "2.11.8",
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

