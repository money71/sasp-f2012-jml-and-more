# OpenJML Code Diving #

Interesting places in the code should be marked with a comment containing "**sasp\_f2012**" (without quotes of course).

## RAC ##

### \nonnullelements ###

Files seeming relevant to us, currently in no particular order.
  * JmlRac.java (annotated)
  * JmlAttr.java (annotated)
  * JmlParser.java (annotated)

Further files working with \nonnullelements:
  * BasicBlocker.java (annotated)
  * JmlAssertionAdder.java (annotated)

Declaration of token for \nunnullelements

```
[...]
BSNONNULLELEMENTS("\\nonnullelements"),
[...]
```

com.sun.tools.javac.parser.JmlTokens.java, l. 144

Search for references to _BSNONNULLELEMENTS_ in the code if you want to look further.

**References to _BSNONNULLELEMENTS_**
  * visitJmlMethodInvocation(JmlMethodInvocation) in JmlAttr.java checks for well-typed annotations, including _BSNONNULLELEMENTS_ (l. 2793).
  * visitJmlMethodInvocation(JmlMethodInvocation) in JmlRac.java calls to translateNonNullArguments() in switch-case of _BSNONNULLELEMENTS_ (l. 1714)
    * translateNonnullelements(JCMethodInvocation tree) in JmlRac.java (l. 1848)

**See org.jmlspecs.openjml.esc.BasicBlocker, l. 3639 - 3731, esp. l. 3702**
It seems that there are some implementations present, the overall connection is currently not clear to me, though.

Comments indicate that a _\forall_ expression might be required or more elegant. Example:

```
//@ requires \nonnullelements o;
```

equals

```
//@ requires \forall o, i; i < o.length; \nonnull o[i];
```

Simply combining both would reduce amount of code needed.



## \nonnullelements in the JML2 refman ##

Quote p. 99 from the pdf version 2011:

  1. .4.14 \nonnullelements
> The syntax of a nonnullelements-expression is as follows. See Section 12.2
> [Expressions](Specification.md), page 90, for the syntax of spec-expression.

> nonnullelements-expression ::= \nonnullelements ( spec-expression )

> The operator \nonnullelements can be used to assert that an array and its
> elements are all non-null. For example, \nonnullelements(myArray), is
> equivalent to [Leino-Nelson-Saxe00]:

```
    myArray != null && 
    (\forall int i; 0 <= i && i < myArray.length; 
    myArray[i] != null) 
```



## rac on Nonnullelements.java ##

todo: make ref to code repos.


When stepping through w. breakpoints we go from the JmlRAC.java (where we have
to hook in) and landing at JmlCompiler.java - here the (toString) of the tree
is looking like:

```

public class NonNullElements {
  
  public NonNullElements() {
    super();
    .java.lang.Exception _JML$$$signalsException = null;
    try {
    } catch (.java.lang.RuntimeException _JML$$$caughtException) {
      _JML$$$signalsException = _JML$$$caughtException;
      throw _JML$$$caughtException;
    } finally {
      if (_JML$$$signalsException == null) {
      } else {
      }
      _JML$$$checkInvariant$$NonNullElements();
      _JML$$$checkStaticInvariant();
    }
  }
    /*@
      requires \nonnullelements(a); 
   */

  public static void foo(Object[] a) {
    boolean _JML$$$PRE28579615 = false;
    try {
      {
        _JML$$$PRE28579615 = true && a != null && org.jmlspecs.utils.Utils.nonnullElementCheck(a);
        if (!(false | _JML$$$PRE28579615)) org.jmlspecs.utils.Utils.assertionFailure("/home/ubuntu/open_jml_branch_workspace/JMLExamples/src/NonNullElements.java:4: JML precondition is false");
      }
    } catch (.java.lang.Exception _JML$$$caughtException) {
      org.jmlspecs.utils.Utils.assertionFailure("/home/ubuntu/open_jml_branch_workspace/JMLExamples/src/NonNullElements.java:4: JML precondition is undefined - exception thrown");
    }
    _JML$$$checkStaticInvariant();
    .java.lang.Exception _JML$$$signalsException = null;
    try {
    } catch (.java.lang.RuntimeException _JML$$$caughtException) {
      _JML$$$signalsException = _JML$$$caughtException;
      throw _JML$$$caughtException;
    } finally {
      if (_JML$$$signalsException == null) {
      } else {
        try {
          if (true) org.jmlspecs.utils.Utils.assertionFailure("/home/ubuntu/open_jml_branch_workspace/JMLExamples/src/NonNullElements.java:4: JML unexpected exception");
        } catch (.java.lang.Exception _JML$$$caughtException) {
          org.jmlspecs.utils.Utils.assertionFailure("/home/ubuntu/open_jml_branch_workspace/JMLExamples/src/NonNullElements.java:4: JML default signals_only condition is undefined - exception thrown");
        }
      }
      _JML$$$checkStaticInvariant();
    }
  }
  
  public static void main(String[] args) {
    boolean _JML$$$PRE28053363 = false;
    try {
      {
        _JML$$$PRE28053363 = true && args != null;
        if (!(false | _JML$$$PRE28053363)) org.jmlspecs.utils.Utils.assertionFailure("/home/ubuntu/open_jml_branch_workspace/JMLExamples/src/NonNullElements.java:8: JML precondition is false");
      }
    } catch (.java.lang.Exception _JML$$$caughtException) {
      org.jmlspecs.utils.Utils.assertionFailure("/home/ubuntu/open_jml_branch_workspace/JMLExamples/src/NonNullElements.java:8: JML precondition is undefined - exception thrown");
    }
    _JML$$$checkStaticInvariant();
    .java.lang.Exception _JML$$$signalsException = null;
    try {
      Object[] array = org.jmlspecs.utils.Utils.nonNullCheck("/home/ubuntu/open_jml_branch_workspace/JMLExamples/src/NonNullElements.java:9: JML null initialization of non_null variable array", new Object[1]);
      array[0] = new Object();
      foo(array);
    } catch (.java.lang.RuntimeException _JML$$$caughtException) {
      _JML$$$signalsException = _JML$$$caughtException;
      throw _JML$$$caughtException;
    } finally {
      if (_JML$$$signalsException == null) {
      } else {
        try {
          if (true) org.jmlspecs.utils.Utils.assertionFailure("/home/ubuntu/open_jml_branch_workspace/JMLExamples/src/NonNullElements.java:8: JML unexpected exception");
        } catch (.java.lang.Exception _JML$$$caughtException) {
          org.jmlspecs.utils.Utils.assertionFailure("/home/ubuntu/open_jml_branch_workspace/JMLExamples/src/NonNullElements.java:8: JML default signals_only condition is undefined - exception thrown");
        }
      }
      _JML$$$checkStaticInvariant();
    }
  }
  
  @Model 
  /*synthetic*/ public void _JML$$$checkInvariant$$NonNullElements() {
    org.jmlspecs.utils.Utils.callClassInvariant(this, "java.lang.Object");
  }
  
  @Model 
  /*synthetic*/ public static void _JML$$$checkStaticInvariant() {
    org.jmlspecs.utils.Utils.callStaticClassInvariant("java.lang.Object");
  }
  // JML specifications
  
  @Model 
  /*synthetic*/ public void _JML$$$checkInvariant$$NonNullElements() {
    org.jmlspecs.utils.Utils.callClassInvariant(this, "java.lang.Object");
  }
  
  @Model 
  /*synthetic*/ public static void _JML$$$checkStaticInvariant() {
    org.jmlspecs.utils.Utils.callStaticClassInvariant("java.lang.Object");
  }
}

```


Looking carefully at the tree indicates that the nonnullelements already is
implemented: **org.jmlspecs.utils.Utils.nonnullElementCheck(a);**

Looking up the OpenJML code:

```

    /** Tests that an array and all the elements of the array are non-null 
     * @param array the array to test
     * @return true if all elements are not null, false if at least one is
     */  // FIXME - this is a different style from the others - it emits no message
    public static boolean nonnullElementCheck(Object[] array) {
        if (array == null) return false;
        for (Object o: array) {
            if (o == null) return false;
        }
        return true;
    }

```






