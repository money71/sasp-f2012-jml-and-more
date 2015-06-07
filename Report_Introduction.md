# Introduction #

This project report for the course Advanced Models and Program in spring 2012 documents our efforts to extend the OpenJML framework. Our project focuses on implementing quantified statements into the runtime assertion checker of OpenJML.

## An overview of OpenJML ##
OpenJML is a tool to verify the correctness of Java 7 code by specifying the behaviour of classes and methods using mathematical models. [1,2] It is built on top of the OpenJDK compiler [3](3.md) and has a Java-like syntax (the JML syntax) to add pre- and post-conditions to source code as well as invariants. These conditions are written by the developer in comments throughout the sources or in a separate file. The tool then comes with three different variants to check the correctness of source code specifications:

  * Static analysis
  * Extended static analysis (ESC)
  * Runtime assertion checker (RAC)

While the static analysis only checks the correctness of the JML statements, the ESC is able to verify the correctness of the progam's behavior to a certain extend by implying automated like Yices or interactive provers like Coq. [1,4,4b]

The RAC compiles the JML specifications in to the binary code and checks that invariants and pre- and post-conditions hold during executing the program. As the OpenJDK compiler is part of OpenJML, the AST generated during compile-time is altered so that actual assertions will be executed before and after each call of a method. Using additional tools, it is possible to generate test-suites for the RAC-compiled Java binaries to quickly get huge coverage of unit testing. [4c,5]

## Overview of the Report ##

In this project, we have investigated and implemented a solution for evaluating quantified statements over integers. In the current OpenJML trunk version [6.], quantified statements can only be evaluated for one race variable. As the ESC of OpenJML is currently being overhauled entirely, we focussed on developing a solution for the OpenJML RAC.

In the following report, we will outline the problem further and give examples of currently not evaluated quantified statements. For brevity, we will focus only on the implementation of the  _\forall_ expression. Next we will describe a number of possible solutions, starting with the most naive approach, and explain our design decisions in the solution. We will then explain our solution in detail, followed by a section to outline future work on our proposed solution.