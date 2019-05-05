---
layout: mainpage
projectname: Renaissance Suite
logoname: mona-lisa-round.png
title: Documentation
permalink: /docs.html
---


# Documentation Overview

Thank you for your interest in using the Renaissance Benchmark Suite!
<br/>
On this page, we provide basic usage instructions, and other useful information.

- [Getting Started with Renaissance](#getting-started)
- [Contributing to Renaissance](#contribution-guide)
- [Licensing Information](#licensing)

The motivation behind the Renaissance benchmark suite,
as well as the detailed analysis of the individual benchmarks,
are described in the following [PLDI'19 paper](/resources/docs/renaissance-suite.pdf).


# <a name="getting-started"></a> Getting Started with Renaissance

The Renaissance Benchmark Suite comes with an informative guide
on how to run Renaissance benchmarks, how to add new benchmarks, run policies and plugins,
and a technical overview of the internal design of the suite.

<div id="readme-holder">
</div>
<script>
loadRemoteContent(
  "readme-holder",
  "https://api.github.com/repos/{{ site.githubOrg }}/{{ site.githubRepo }}/contents/README.md",
  "{{ page.logoname }}",
  "markdown"
)
</script>

The source file that explains how to use Renaissance can be found
[here](
https://github.com/{{ site.githubOrg }}/{{ site.githubRepo }}/blob/master/README.md
).


# <a name="contribution-guide"></a> Contributing to Renaissance

One of the aims of the Renaissance suite is to continually evolve,
and maintain a collection of relevant and interesting benchmarks
for VM, compiler and tool developers.
Renaissance therefore relies on an open-source contribution process
to derive the set of benchmarks that are useful when optimizing or analyzing the JVM behaviour.
The contribution guide contains detailed information about this process.

<div id="contribution-holder">
</div>
<script>
loadRemoteContent(
  "contribution-holder",
  "https://api.github.com/repos/{{ site.githubOrg }}/{{ site.githubRepo }}/contents/CONTRIBUTION.md",
  "{{ page.logoname }}",
  "markdown"
)
</script>

The source file that explains the contribution process for the Renaissance suite can be found
[here](
https://github.com/{{ site.githubOrg }}/{{ site.githubRepo }}/blob/master/CONTRIBUTION.md
).


# <a name="licensing"></a> Licensing Information

The Renaissance Benchmark Suite comes in two distributions,
and is available under two licenses: the MIT license, and the GPL3 license.
Depending on your needs, you can choose either of these licenses.
The set of benchmarks in the Renaissance distribution with the MIT license is a subset of the
benchmarks in the GPL3 distribution.


## MIT Distribution

The MIT license file can be found
[here](
https://github.com/{{ site.githubOrg }}/{{ site.githubRepo }}/blob/master/LICENSE.MIT
).

<div id="license-holder-mit">
</div>
<script>
loadRemoteContent(
  "license-holder-mit",
  "https://api.github.com/repos/{{ site.githubOrg }}/{{ site.githubRepo }}/contents/LICENSE.MIT",
  "{{ page.logoname }}",
  "license"
)
</script>


## GPL3 Distribution

The GPL3 license file can be found
[here](
https://github.com/{{ site.githubOrg }}/{{ site.githubRepo }}/blob/master/LICENSE.GPL
).

<div id="license-holder-gpl">
</div>
<script>
loadRemoteContent(
  "license-holder-gpl",
  "https://api.github.com/repos/{{ site.githubOrg }}/{{ site.githubRepo }}/contents/LICENSE.GPL",
  "{{ page.logoname }}",
  "license"
)
</script>
