# IDE development

## IntelliJ

In order to work on the project with IntelliJ, one needs to install the following plugins :
  - `Scala` : part of the codebase uses Scala and Renaissance is organized in sbt projects.
  - `scalafmt` (optional) : adds an action that can be triggered with `Code -> Reformat with scalafmt`
  which will reformat the code according to the formatting rule defined in `.scalafmt.conf`
  (same as the `renaissanceFormat` sbt task).

Then, the root of the repository can be opened as an IntelliJ project.
