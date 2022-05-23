# Making a release

This is just an internal memo describing how to make a Renaissance
release so that people don't have to re-discover the process with
every release :-)

## Phase 1

To make a release, you first need to put on your wordsmith hat:

- [ ] Create a draft release on GitHub.
  - Can be more terse than the web site release announcement.
  - Usually highlights and links to important pull requests.
- [ ] Write an announcement for the web.
  - Bit more verbose/less technical than the GitHub release announcement.
  - Keep the main message in the **first paragraph**, because that's
    what gets displayed on the front page.
  - `website/YYYY-MM-DD-renaissance-<maj>-<min>-<patch>.md`
- [ ] Create a PR for the announcement in the Renaissance
    [website repository](https://github.com/renaissance-benchmarks/renaissance-benchmarks.github.io)
  - Don't merge it until you make the GitHub release (wait for phase 3)

## Phase 2

With the prose done, you can proceed with the technicalities of
making a release. These can be eventually automated:

- [ ] Build the Renaissance bundle using a version number
  override corresponding to the upcoming release:
  - `sbt -Dproject.version=<version> renaissancePackage`
- [ ] Update `README.md` in the project root by running:
  - `java -jar target/renaissance-gpl-<version>.jar --readme`
- [ ] Manually update version numbers in files that are not generated:
  - `plugins/jmx-memory/README.md`
  - `plugins/jmx-timers/README.md`
  - `plugins/ubench-agent/README.md`
- [ ] Set `git.baseVersion` in `version.sbt` to the next version **after**
  the release version. This provides a reasonable base version for 
  *git-less* operation.
- [ ] Commit the changes locally, directly to the `master` branch
  of the repository.
- [ ] Tag the HEAD commit using an **annotated tag**. The annotated
  tag with a `v` prefix is used by `git describe` and `sbt-git` plugin to
  automatically determine the project version.
  - `git tag v<version> -m "Renaissance <version>"`
  - Don't forget the `v` prefix in the tag name.

At this point, the release is marked in the code base and from now on, the
automatic version numbers will be relative to the latest version tag. Now
is the time to build the artifacts that will be attached to the GitHub release
and publish the releases on GitHub and on the Renaissance web site.

- [ ] Make sure you are using JDK8 to build the artifacts.
  - Even though we currently support LTS releases up to and including JDK17,
    using the lowest supported version ensures that nothing in the build chain
    decides to target a newer JDK.
- [ ] Make sure to clean the repository and recreate useful symlinks.
  - `git clean -dxf`
  - `ln -s tools/sbt/bin/sbt sbt`
- [ ] Build both the GPL and MIT bundles.
  - `./sbt 'renaissancePackage; set nonGplOnly := true; renaissancePackage'`
  - If everything went well, you should end up with the following files:
    - `target/renaissance-gpl-<version>.jar`
    - `target/renaissance-mit-<version>.jar`
- [ ] Build the plugins to make them a bit more accessible to people. Because
  SBT does not support `-C` alà `make`, you can use the following commands
  (assuming you have a `sbt` symlink in the project root).
  - `pushd plugins/jmx-memory && { ../../sbt assembly; popd; }`
  - `pushd plugins/jmx-timers && { ../../sbt assembly; popd; }`
  - `pushd plugins/ubench-agent && { ./build-ubench-agent.sh && ../../sbt assembly; popd; }`
  - If everything went well, you should end up with the following files
    with plugin-specific version numbers:
    - `plugins/jmx-memory/target/plugin-jmxmemory-assembly-<ver>.jar`
    - `plugins/jmx-timers/target/plugin-jmxtimers-assembly-<ver>.jar`
    - `plugins/ubench-agent/target/plugin-ubenchagent-assembly-<ver>.jar`
  - Note that we do not distribute the `libubench-agent.so` library because
    it depends on local installation of PAPI and is quite fragile.
- [ ] Attach all the artifacts to the GitHub release draft.

## Phase 3

This phase makes the previous steps actually visible. If you managed to
build the artifacts, proceed as follows:

- [ ] Push the changes in the `master` branch of the Renaissance repository
  to GitHub, **including** the annotated release tag.
  - This requires that you momentarily allow administrators to push
    to the `master` branch (it is normally disabled).
  - Edit the branch protection rules for the `master` branch on the
    [Branches](https://github.com/renaissance-benchmarks/renaissance/settings/branches)
    page and turn off the **Include administrators** setting in the 
    **Protect matching branches** section.
  - `git push --tags origin master`
- [ ] Preferably wait until CI finishes playing with the `master` branch,
  hoping the badges on the main page of the web site stay green.
- [ ] Select tag in the GitHub release draft and publish the release.
- [ ] Merge the release announcement PR to the `master` branch
  of the web site repository to publish it.
