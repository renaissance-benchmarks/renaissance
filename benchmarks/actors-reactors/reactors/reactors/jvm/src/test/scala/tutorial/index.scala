/*!md
---
layout: tutorial
title: Reactors
topic: reactors
logoname: reactress-mini-logo-flat.png
projectname: Reactors.IO
homepage: http://reactors.io
permalink: /reactors/index.html
---


Examples in this guide work with multiple language frontends: Java, Scala and
Scala.js. By default, code snippets are shown using the Scala syntax,
which is equivalent to Scala.js (modulo a few platform-specific differences,
which are noted in respective cases).
To show the Java version of each snippet, click on the toggle found below the code.

The guide is being created incrementally as we go,
and the features of the framework may at any time be only partially covered.
If you would like to see documentation for a particular feature,
please consider submitting a patch at
[the Reactors repo at GitHub](https://github.com/reactors-io/reactors).

All code examples are tested as part of the continuous integration process,
and they can be found
[here](https://github.com/reactors-io/reactors/tree/master/reactors).


## Table of Contents

### Introduction

{% for pg in site.pages %}
  {% if pg.topic == "reactors" and pg.section == "guide-intro" and pg.pagetot %}
    {% assign totalPages = pg.pagetot %}
  {% endif %}
{% endfor %}

<ul>
{% for i in (1..totalPages) %}
  {% for pg in site.pages %}
    {% if pg.topic == "reactors" and pg.section == "guide-intro" %}
      {% if pg.pagenum and pg.pagenum == i %}
        <li><a href="/tutorialdocs/{{ pg.url }}">{{ pg.title }}</a></li>
      {% endif %}
    {% endif %}
  {% endfor %}
{% endfor %}
</ul>


### Reactors

{% for pg in site.pages %}
  {% if pg.topic == "reactors" and pg.section == "guide-main" and pg.pagetot %}
    {% assign totalPages = pg.pagetot %}
  {% endif %}
{% endfor %}

<ul>
{% for i in (1..totalPages) %}
  {% for pg in site.pages %}
    {% if pg.topic == "reactors" and pg.section == "guide-main" %}
      {% if pg.pagenum and pg.pagenum == i %}
        <li><a href="/tutorialdocs/{{ pg.url }}">{{ pg.title }}</a></li>
      {% endif %}
    {% endif %}
  {% endfor %}
{% endfor %}
</ul>


### Reactor Protocols

{% for pg in site.pages %}
  {% if pg.topic == "reactors" and pg.section == "guide-protocol" and pg.pagetot %}
    {% assign totalPages = pg.pagetot %}
  {% endif %}
{% endfor %}

<ul>
{% for i in (1..totalPages) %}
  {% for pg in site.pages %}
    {% if pg.topic == "reactors" and pg.section == "guide-protocol" %}
      {% if pg.pagenum and pg.pagenum == i %}
        <li><a href="/tutorialdocs/{{ pg.url }}">{{ pg.title }}</a></li>
      {% endif %}
    {% endif %}
  {% endfor %}
{% endfor %}
</ul>


### Utilities

{% for pg in site.pages %}
  {% if pg.topic == "reactors" and pg.section == "guide-util" and pg.pagetot %}
    {% assign totalPages = pg.pagetot %}
  {% endif %}
{% endfor %}

<ul>
{% for i in (1..totalPages) %}
  {% for pg in site.pages %}
    {% if pg.topic == "reactors" and pg.section == "guide-util" %}
      {% if pg.pagenum and pg.pagenum == i %}
        <li><a href="/tutorialdocs/{{ pg.url }}">{{ pg.title }}</a></li>
      {% endif %}
    {% endif %}
  {% endfor %}
{% endfor %}
</ul>

!*/
package tutorial
