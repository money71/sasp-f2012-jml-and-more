# Getting into OpenJML Development #

## Quantified expressions ##

These may be interesting entry points for us:
  * org.jmlspecs.openjml.esc.JmlAssertionAdder.java, line 1792
  * org.jmlspecs.openjml.JmlTree.java, line 2112
  * com.sun.tools.javac.comp.JmlRac.java, line 747
  * org.jmlspecs.openjml.JmlCompiler.java

> Questions
    * In how far are quantifiers implemented already?

## Implementation Walkthrough ##

### Original ForAll.java ###

```
public class ForAll {
	
	//@ requires (\forall int i; 0 <= i && i < array.length; array[i] == i);
	public static void forAll (int[] array) {
		// Do nothing
	}
	
	public static void main (String[] args) {
		forAll(new int[] {0, 1, 2, 3});
	}
	
}
```


### AST-modified code by OpenJML RAC (copy-pasted from the debugger) ###

```
public class ForAll {
  
  public ForAll() {
    super();
  }
    /*@
      requires (\forall int i; 0 <= i && i < array.length; array[i] == i); 
   */

  public static void forAll(int[] array) {
  }
  
  public static void main(String[] args) {
    forAll(new int[]{0, 1, 2, 3});
  }
  // JML specifications
  
  @Model 
  /*synthetic*/ public void _JML$$$checkInvariant$$ForAll() {
  }
  
  @Model 
  /*synthetic*/ public static void _JML$$$checkStaticInvariant() {
  }
}
```

### Conclusions ###

  * ~~There seems to be actual no implementation of _\forall_ quantifiers in OpenJML RAC~~
  * Tests with RAC compiled classes indicate that quantifiers in fact are implemented for arbitrary Objects over classes implementing _Collection_

## RAC Overview ##

Cosider a file Foo.java containing a method with JML annotations

```
//@ invariant a;
//@ requires b;
//@ ensures c;
public void foo() {
       // Some code
}
```

To compile this for RAC, the following procedure is executed:

  * jmlc Foo.java
    * Transforms source into an AST from which new sources are generated
  * javac -cp $CLASSPATH:org.jmlspecs.models.jar:org.jmlspecs.runtime.jar Foo$rac$.java
    * -P stops at this point and outputs a file Foo.java.gen containing the generated sources

The resulting sources should in essence feel like this:

```
public void fooRAC() {
       assert (a);
       assert (b);
       foo();
       assert (a);
       assert (c);
}
```

These sources can then be run like normal java-compiled code, but require the same jars used for compiling.

  * jmlrac Foo
    * java -cp $CLASSPATH:org.jmlspecs.models.jar:org.jmlspecs.runtime.jar Foo



## JML 2 quantifiers ##

the grammar def:

```
    12.4.24 Quantified Expressions 
    spec-quantified-expr ::= ( quantifier quantified-var-decls ;
                         [ [ predicate ] ; ] 
                         spec-expression ) 
    quantifier ::= \forall | \exists 
               | \max | \min 
               | \num_of | \product | \sum 
    quantified-var-decls ::= [ bound-var-modifiers ] type-spec quantified-var-declarator 
                         [ , quantified-var-declarator ] . . . 
    quantified-var-declarator ::= ident [ dims ] 
    spec-variable-declarators ::= spec-variable-declarator 
                              [ , spec-variable-declarator ] . . . 
    spec-variable-declarator ::= ident [ dims ] 
                             [ = spec-initializer ] 
    spec-array-initializer ::= { [ spec-initializer 
                           [ , spec-initializer ] . . . [ , ] ] } 
    spec-initializer ::= spec-expression 
                     | spec-array-initializer 
```

from jml ref man: http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_12.html#SEC153



## JML 2 quantifiers rac implementation ##

Code is in the cvs repos of jml - http://jmlspecs.cvs.sourceforge.net/jmlspecs

The quantifier package is explained here :
- http://jmlspecs.cvs.sourceforge.net/viewvc/jmlspecs/JML2/org/jmlspecs/jmlrac/qexpr/package.html
- http://jmlspecs.cvs.sourceforge.net/viewvc/jmlspecs/JML2/org/jmlspecs/jmlrac/qexpr/

they perform a statical analysis splitting up the type:
- EnumerationBased
> - boolean
- IntervalBased
> - int
> - char
> (not floats)
- SetBased
> - objects

It confuses us a bit that its called statical analysis because its in the rac ~~and
the expressions seems to be evaluated~~. ??


### org/jmlspecs/jmlrac ###

They have a **quantiExp** which they test isForAll() | isExists() | isSum() etc..

code of interest: TransQuantifiedExpression.java and

### qexpr/StaticAnalysis.java ###

```
   /** Returns Java source code for evaluating the JML quantified
     * expression, which is either a universal or existential
     * quantifier.  Refer to the method <code>translateForAll</code>
     * and <code>translateExists</code> for the structure of the
     * returned code.
     *
     * <pre><jml>
     * requires quantiExp.isForAll() || quantiExp.isExists();
     * ensures \result != null;
     * </jml></pre>
     *
     * @see #translateForAll()
     * @see #translateExists()
     */
    private RacNode transForAllOrExists() 
    throws NonExecutableQuantifierException 
    {
    	final boolean isForAll = quantiExp.isForAll();
    	final String cond = (isForAll ? "" : "!") +  resultVar;
    	final String initVal = isForAll ? "true" : "false";
    	
    	// build code for evaluating the body, i.e.,
    	// P ==> Q for (\forall D; P; Q) and P && Q for (\exists D; P; Q).
    	JExpression expr = unwrapJmlExpression(quantiExp.specExpression());
    	final JmlPredicate pred = quantiExp.predicate();
    	if (pred != null) {
    		if (isForAll)
    			expr = new JmlRelationalExpression(NO_REF, OPE_IMPLIES,
    					pred, expr);
    		else
    			expr = new JConditionalAndExpression(NO_REF, pred, expr);
    	}
    	RacNode result = transExpression(expr, resultVar);
    	
    	// build code for while loops to evaluate the body
    	JVariableDefinition[] varDefs = quantiExp.quantifiedVarDecls();
    	for (int i = varDefs.length - 1; i >= 0; i--) {
    		result = generateLoop(varDefs[i], rangePredicate(), cond, result);
    	}
    	
    	// wrap the resulting code in try statement
    	if(transExp instanceof TransExpression){
    		result = RacParser.parseStatement(
    				"try {\n" +
    				"  " + resultVar + " = " + initVal + ";\n" +
    				"$0\n" +
    				"}\n" +
    				"catch (JMLNonExecutableException " + varGen.freshVar() + ") {\n" +
    				"  " + context.angelicValue(resultVar) + ";\n" + 
    				"}\n" +
    				"catch (java.lang.Exception " + varGen.freshVar() + ") {\n" +
    				"  " + context.demonicValue(resultVar) + ";\n" + 
    				"}",
    				result.incrIndent());
    	}
    	return result;
    }
```



## Example of an source file w. quantifiers (JML 2) ##

- BinSearch http://code.google.com/p/sasp-f2012-jml-and-more/source/browse/JMLExamples/trunk/examples/dk/itu/jmlexamples/binsearch/BinSearch.java
- the gen (using option (-P**) http://code.google.com/p/sasp-f2012-jml-and-more/source/browse/JMLExamples/trunk/jml-compiled/dk/itu/jmlexamples/binsearch/BinSearch.java.gen
> code pasted here for now based on (revision: [r10](https://code.google.com/p/sasp-f2012-jml-and-more/source/detail?r=10))**


```

package dk.itu.jmlexamples.binsearch;

import org.jmlspecs.lang.*;
import org.jmlspecs.jmlrac.runtime.*;


public class BinSearch extends java.lang.Object implements JMLCheckable {


  private static int internal$search(int[] array, int target) {
    int low = 0;
    int high = array.length;
    int mid;

    while (low  <  high) {
      mid = (low + high) / 2;
      if (target  <  array[mid]) {
        high = mid - 1;
      } else if (target  >  array[mid]) {
        low = mid + 1;
      } else {
        return mid;
      }
    }

    return -1;
  }


  private static void internal$main(java.lang.String[] args) {
    int[] a = 
    {1, 2, 3};
    int result = search(a, 2);

    System.out.println("result: " + result);
  }

  /** Generated by JML to check static invariants of 
   * class BinSearch. */
  public static void checkInv$static(java.lang.String rac$msg) {
  }

  /** Generated by JML to check non-static invariants of 
   * class BinSearch. */
  public void checkInv$instance$BinSearch(java.lang.String rac$msg) {
    java.util.Set rac$where = new java.util.HashSet();
    boolean rac$b = true;
    boolean rac$bSuper = true;
    if (!rac$b) {
      JMLChecker.exit();
      throw new JMLInvariantError("BinSearch", rac$msg, rac$where);
    }
  }

  /** Generated by JML to check static constraints of 
   * class BinSearch. */
  public static void checkHC$static(java.lang.String rac$msg,
    java.lang.String rac$name, java.lang.Class[] rac$params) {
  }

  /** Generated by JML to check non-static constraints of 
   * class BinSearch. */
  public void checkHC$instance$BinSearch(java.lang.String rac$msg,
    boolean rac$private, java.lang.String rac$name, java.lang.Class[] rac$params) {
    rac$name = rac$private ? null : rac$name;
  }

  /** Generated by JML to check non-static constraints of 
   * class BinSearch. */
  public void checkHC$instanceW$BinSearch(java.lang.String rac$msg,
    java.lang.String rac$name, java.lang.Class[] rac$params) {
  }

  /** Generated by JML to check non-static constraints of 
   * class BinSearch. */
  public void checkHC$instanceS$BinSearch(java.lang.String rac$msg,
    java.lang.String rac$name, java.lang.Class[] rac$params) {
  }

  /** Generated by JML to evaluate, in the pre-state,
   * the old expressions appearing in the static constraints
   * of class BinSearch. */
  public static void evalOldExprInHC$static() {
  }

  /** Generated by JML to evaluate, in the pre-state,
   * the old expressions appearing in the non-static constraints
   * of class BinSearch. */
  public void evalOldExprInHC$instance$BinSearch() {
  }


  public BinSearch() {
    rac$dented = true;
    // skip assertion checking during initialization
    if (!rac$ClassInitialized || !rac$initialzed) {
      internal$$init$();
      return;
    }
    if (!(JMLChecker.isActive(JMLChecker.PRECONDITION) && rac$dented())) {
      internal$$init$();
      return;
    }
    // check static invariant
    if (JMLChecker.isActive(JMLChecker.INVARIANT) && rac$dented()) {
      JMLChecker.enter();
      checkInv$static("<init>@pre<File \"<GENERATED-BY-mjc>\", line 0>");
      JMLChecker.exit();
    }
    // check precondition
    if (JMLChecker.isActive(JMLChecker.PRECONDITION)) {
      JMLChecker.enter();
      checkPre$$init$$BinSearch();
      JMLChecker.exit();
    }
    // eval old exprs in constraint
    if (JMLChecker.isActive(JMLChecker.CONSTRAINT) && rac$dented()) {
      JMLChecker.enter();
      evalOldExprInHC$static();
      JMLChecker.exit();
    }
    boolean rac$ok = true;
    boolean rac$inv = true;
    try {
      internal$$init$();
      // check normal postcondition
      if (JMLChecker.isActive(JMLChecker.POSTCONDITION) && rac$dented()) {
        JMLChecker.enter();
        checkPost$$init$$BinSearch(null);
        JMLChecker.exit();
      }
    }
    catch (JMLEntryPreconditionError rac$e) {
      rac$ok = false;
      throw new JMLInternalPreconditionError(rac$e);
    }
    catch (JMLAssertionError rac$e) {
      rac$ok = false;
      throw rac$e;
    }
    catch (java.lang.Throwable rac$e) {
      rac$inv = false;
      try {
        // check exceptional postcondition
        if (JMLChecker.isActive(JMLChecker.POSTCONDITION) && rac$dented()) {
          JMLChecker.enter();
          checkXPost$$init$$BinSearch(rac$e);
          JMLChecker.exit();
        }
      }
      catch (JMLAssertionError rac$e1) {
        rac$ok = false;
        throw rac$e1;
      }
    }
    finally {
      if (rac$ok && rac$inv) {
        // check instance invariant
        if (JMLChecker.isActive(JMLChecker.INVARIANT) && rac$dented()) {
          JMLChecker.enter();
          checkInv$instance$BinSearch("<init>@post<File \"<GENERATED-BY-mjc>\", line 0>");
          JMLChecker.exit();
        }
      }
      if (rac$ok) {
        // check static invariant
        if (JMLChecker.isActive(JMLChecker.INVARIANT) && rac$dented()) {
          JMLChecker.enter();
          checkInv$static("<init>@post<File \"<GENERATED-BY-mjc>\", line 0>");
          JMLChecker.exit();
        }
        // check static constraint
        if (JMLChecker.isActive(JMLChecker.CONSTRAINT) && rac$dented()) {
          JMLChecker.enter();
          checkHC$static("<init>@post<File \"<GENERATED-BY-mjc>\", line 0>", "<init>", new java.lang.Class[] { });
          JMLChecker.exit();
        }
      }
    }
  }

  /** Generated by JML to check the precondition of
   * method BinSearch. */
  public boolean checkPre$$init$$BinSearch() {
    return false;
  }

  /** Generated by JML to check the normal postcondition of
   * method BinSearch. */
  public void checkPost$$init$$BinSearch(final java.lang.Object rac$result) {
  }

  /** Generated by JML to check the exceptional postcondition of
   * method BinSearch. */
  public void checkXPost$$init$$BinSearch(final java.lang.Throwable rac$e) {
    JMLChecker.exit();
    if (rac$e instanceof java.lang.RuntimeException) {
        throw (java.lang.RuntimeException) rac$e;
    }
    if (rac$e instanceof java.lang.Error) {
        throw (java.lang.Error) rac$e;
    }
  }

  /** Generated by JML to wrap assertion check code to
   * the constructor of the same signature. */
  private void internal$$init$() {
  }

  /** Generated by JML to check the precondition of
   * method search. */
  public static boolean checkPre$search$BinSearch(final int[] array, final int target) {
    java.util.Set rac$where = new java.util.HashSet();
    boolean rac$b = false;
    // Alternative Translation
    try {
      class rac$v2{public boolean eval(){
      boolean rac$v0 = false ;
      int i = 0;
      int rac$v1 = 0;
      i = 0;
      rac$v1 = array.length;
      rac$v0 = false;
      while (!rac$v0 && i < rac$v1) {
        rac$v0 = (((i >= 0) && (i < array.length)) && (array[i] == target));
        i = i + 1;
      }
      return rac$v0;
      }}
      rac$v2 rac$v0Evaluator = new rac$v2();
      class rac$v5{public boolean eval(){
      boolean rac$v3 = false ;
      int i = 0;
      int rac$v4 = 0;
      i = 0;
      rac$v4 = (array.length - 1);
      rac$v3 = true;
      while (rac$v3 && i < rac$v4) {
        rac$v3 = (!(((i >= 0) && (i < (array.length - 1)))) || (array[i] <= array[(i + 1)]));
        i = i + 1;
      }
      return rac$v3;
      }}
      rac$v5 rac$v3Evaluator = new rac$v5();
      rac$pre0 = ((array != null) && (((array != null) && rac$v0Evaluator.eval()) && rac$v3Evaluator.eval()));
    } catch (JMLNonExecutableException rac$v6$nonExec) {
    	rac$pre0 = true; 
    } catch (Throwable rac$v7$cause) {
    	JMLChecker.exit();
    	throw new JMLEvaluationError("Invalid Expression in \"<GENERATED-BY-mjc>\", line 0, character 0", new JMLEntryPreconditionError(rac$v7$cause)); 
    }
    rac$b = rac$b || rac$pre0;
    // Alternative Translation
    try {
      class rac$v10{public boolean eval(){
      boolean rac$v8 = false ;
      int i = 0;
      int rac$v9 = 0;
      i = 0;
      rac$v9 = array.length;
      rac$v8 = true;
      while (rac$v8 && i < rac$v9) {
        rac$v8 = (!(((i >= 0) && (i < array.length))) || (array[i] != target));
        i = i + 1;
      }
      return rac$v8;
      }}
      rac$v10 rac$v8Evaluator = new rac$v10();
      rac$pre1 = ((array != null) && ((array != null) && rac$v8Evaluator.eval()));
    } catch (JMLNonExecutableException rac$v11$nonExec) {
    	rac$pre1 = true; 
    } catch (Throwable rac$v12$cause) {
    	JMLChecker.exit();
    	throw new JMLEvaluationError("Invalid Expression in \"<GENERATED-BY-mjc>\", line 0, character 0", new JMLEntryPreconditionError(rac$v12$cause)); 
    }
    rac$b = rac$b || rac$pre1;
    if (!rac$b) {
      if (JMLChecker.getLevel() > JMLChecker.PRECONDITION) {
        saveTo$rac$stack0();
      }
      JMLChecker.exit();
      throw new JMLEntryPreconditionError("BinSearch", "search", rac$where);
    }
    if (JMLChecker.getLevel() > JMLChecker.PRECONDITION) {
      saveTo$rac$stack0();
    }
    return true;
  }

  /** Generated by JML to check the normal postcondition of
   * method search. */
  public static void checkPost$search$BinSearch(final int[] array, final int target, final int rac$result) {
    restoreFrom$rac$stack0();
    java.util.Set rac$where = new java.util.HashSet();
    boolean rac$b = true;
    boolean rac$b0 = true;
    if (rac$pre0) {
      // Alternative Translation
      try {
        rac$b0 = (rac$result >= 0);
      } catch (JMLNonExecutableException rac$v0$nonExec) {
      	rac$b0 = true; 
      } catch (Throwable rac$v1$cause) {
      	JMLChecker.exit();
      	throw new JMLEvaluationError("Invalid Expression in \"BinSearch.java\", line 17, character 32", new JMLExitNormalPostconditionError(rac$v1$cause)); 
      }
    }
    rac$b = rac$b && rac$b0;
    boolean rac$b2 = true;
    if (rac$pre1) {
      // Alternative Translation
      try {
        rac$b2 = (rac$result == -1);
      } catch (JMLNonExecutableException rac$v4$nonExec) {
      	rac$b2 = true; 
      } catch (Throwable rac$v5$cause) {
      	JMLChecker.exit();
      	throw new JMLEvaluationError("Invalid Expression in \"BinSearch.java\", line 22, character 32", new JMLExitNormalPostconditionError(rac$v5$cause)); 
      }
    }
    rac$b = rac$b && rac$b2;
    if (!rac$b) {
      JMLChecker.exit();
      throw new JMLExitNormalPostconditionError("BinSearch", "search", rac$where);
    }
  }

  /** Generated by JML to check the exceptional postcondition of
   * method search. */
  public static void checkXPost$search$BinSearch(final int[] array, final int target, final java.lang.Throwable rac$e) {
    restoreFrom$rac$stack0();
    java.util.Set rac$where = new java.util.HashSet();
    boolean rac$b = true;
    if (rac$e instanceof java.lang.Exception) {
      java.lang.Exception jml$e = (java.lang.Exception) rac$e;
      boolean rac$b1 = true;
      if (rac$pre0) {
        // Alternative Translation
        try {
          rac$b1 = false;
        } catch (JMLNonExecutableException rac$v2$nonExec) {
        	rac$b1 = true; 
        } catch (Throwable rac$v3$cause) {
        	JMLChecker.exit();
        	throw new JMLEvaluationError("Invalid Expression in \"BinSearch.java\", line 16, character 24", new JMLExitExceptionalPostconditionError(rac$v3$cause)); 
        }
      }
      if (!rac$b1) {
         rac$where.add("\tFile \"src/dk/itu/jmlexamples/binsearch/BinSearch.java\", line 16, character 24, when" + "\n\t\t'jml$e' is " + rac$e);
      }
      rac$b = rac$b && rac$b1;
    }
    if (rac$e instanceof java.lang.Exception) {
      java.lang.Exception jml$e = (java.lang.Exception) rac$e;
      boolean rac$b3 = true;
      if (rac$pre1) {
        // Alternative Translation
        try {
          rac$b3 = false;
        } catch (JMLNonExecutableException rac$v6$nonExec) {
        	rac$b3 = true; 
        } catch (Throwable rac$v7$cause) {
        	JMLChecker.exit();
        	throw new JMLEvaluationError("Invalid Expression in \"BinSearch.java\", line 21, character 24", new JMLExitExceptionalPostconditionError(rac$v7$cause)); 
        }
      }
      if (!rac$b3) {
         rac$where.add("\tFile \"src/dk/itu/jmlexamples/binsearch/BinSearch.java\", line 21, character 24, when" + "\n\t\t'jml$e' is " + rac$e);
      }
      rac$b = rac$b && rac$b3;
    }
    if (!rac$b) {
      JMLChecker.exit();
      throw new JMLExitExceptionalPostconditionError("BinSearch", "search", rac$where);
    }
    JMLChecker.exit();
    if (rac$e instanceof java.lang.RuntimeException) {
        throw (java.lang.RuntimeException) rac$e;
    }
    if (rac$e instanceof java.lang.Error) {
        throw (java.lang.Error) rac$e;
    }
  }

  /** Generated by JML to save pre-values against potential recursive
    * method calls to the method search. */
  private static transient java.util.Stack rac$stack0 = new java.util.Stack();

  /** Generated by JML to save pre-values for the method search. */
  private static void saveTo$rac$stack0() {
    java.lang.Object[] values = new java.lang.Object[2];
    values[0] = new java.lang.Boolean(rac$pre0);
    values[1] = new java.lang.Boolean(rac$pre1);
    rac$stack0.push(values);
  }

  /** Generated by JML to restore pre-values for the method search. */
  private static void restoreFrom$rac$stack0() {
    java.lang.Object[] values = (java.lang.Object[])rac$stack0.pop();
    rac$pre0 = ((java.lang.Boolean) values[0]).booleanValue();
    rac$pre1 = ((java.lang.Boolean) values[1]).booleanValue();
  }

  /** Generated by JML to wrap assertion check code to
   * the method search. */
  public static int search(int[] array, int target) {
    // skip assertion checks during initialization
    if (!rac$ClassInitialized) {
      return internal$search(array, target);
    }
    int rac$result = 0;
    if (!(JMLChecker.isActive(JMLChecker.PRECONDITION))) {
      rac$result = internal$search(array, target);
      return rac$result;
    }
    // eval old exprs in constraint
    if (JMLChecker.isActive(JMLChecker.CONSTRAINT)) {
      JMLChecker.enter();
      evalOldExprInHC$static();
      JMLChecker.exit();
    }
    // check static invariant
    if (JMLChecker.isActive(JMLChecker.INVARIANT)) {
      JMLChecker.enter();
      checkInv$static("search@pre<File \"src/dk/itu/jmlexamples/binsearch/BinSearch.java\", line 12, character 19>");
      JMLChecker.exit();
    }
    // check precondition
    if (JMLChecker.isActive(JMLChecker.PRECONDITION)) {
      JMLChecker.enter();
      checkPre$search$BinSearch(array, target);
      JMLChecker.exit();
    }
    boolean rac$ok = true;
    try {
      // execute original method
      rac$result = internal$search(array, target);
      // check normal postcondition
      if (JMLChecker.isActive(JMLChecker.POSTCONDITION)) {
        JMLChecker.enter();
        checkPost$search$BinSearch(array, target,rac$result);
        JMLChecker.exit();
      }
    }
    catch (JMLEntryPreconditionError rac$e) {
      rac$ok = false;
      throw new JMLInternalPreconditionError(rac$e);
    }
    catch (JMLExitNormalPostconditionError rac$e) {
      rac$ok = false;
      throw new JMLInternalNormalPostconditionError(rac$e);
    }
    catch (JMLExitExceptionalPostconditionError rac$e) {
      rac$ok = false;
      throw new JMLInternalExceptionalPostconditionError(rac$e);
    }
    catch (JMLAssertionError rac$e) {
      rac$ok = false;
      throw rac$e;
    }
    catch ( java.lang.Throwable rac$e) {
      try {
        // check exceptional postcondition
        if (JMLChecker.isActive(JMLChecker.POSTCONDITION)) {
          JMLChecker.enter();
          checkXPost$search$BinSearch(array, target,rac$e);
          JMLChecker.exit();
        }
      }
      catch (JMLAssertionError rac$e1) {
        rac$ok = false;
        throw rac$e1;
      }
    }
    finally {
      if (rac$ok) {
        // check static invariant
        if (JMLChecker.isActive(JMLChecker.INVARIANT)) {
          JMLChecker.enter();
          checkInv$static("search@post<File \"src/dk/itu/jmlexamples/binsearch/BinSearch.java\", line 12, character 19>");
          JMLChecker.exit();
        }
        // check static constraint
        if (JMLChecker.isActive(JMLChecker.CONSTRAINT)) {
          JMLChecker.enter();
          checkHC$static("search@post<File \"src/dk/itu/jmlexamples/binsearch/BinSearch.java\", line 12, character 19>", "search", new java.lang.Class[] { int[].class, java.lang.Integer.TYPE, });
          JMLChecker.exit();
        }
      }
    }
    return rac$result;
  }

  // Generated by JML
  private static transient boolean rac$pre0;
  private static transient boolean rac$pre1;

  /** Generated by JML to check the precondition of
   * method main. */
  public static boolean checkPre$main$BinSearch(final java.lang.String[] args) {
    java.util.Set rac$where = new java.util.HashSet();
    boolean rac$b = false;
    // Alternative Translation
    try {
      rac$pre2 = (args != null);
    } catch (JMLNonExecutableException rac$v0$nonExec) {
    	rac$pre2 = true; 
    } catch (Throwable rac$v1$cause) {
    	JMLChecker.exit();
    	throw new JMLEvaluationError("Invalid Expression in \"BinSearch.java\", line 49, character 39", new JMLEntryPreconditionError(rac$v1$cause)); 
    }
    rac$b = rac$pre2;
    if (!rac$b) {
      if (JMLChecker.getLevel() > JMLChecker.PRECONDITION) {
        saveTo$rac$stack1();
      }
      JMLChecker.exit();
      throw new JMLEntryPreconditionError("BinSearch", "main", rac$where);
    }
    if (JMLChecker.getLevel() > JMLChecker.PRECONDITION) {
      saveTo$rac$stack1();
    }
    return true;
  }

  /** Generated by JML to check the normal postcondition of
   * method main. */
  public static void checkPost$main$BinSearch(final java.lang.String[] args, final java.lang.Object rac$result) {
    restoreFrom$rac$stack1();
  }

  /** Generated by JML to check the exceptional postcondition of
   * method main. */
  public static void checkXPost$main$BinSearch(final java.lang.String[] args, final java.lang.Throwable rac$e) {
    restoreFrom$rac$stack1();
    JMLChecker.exit();
    if (rac$e instanceof java.lang.RuntimeException) {
        throw (java.lang.RuntimeException) rac$e;
    }
    if (rac$e instanceof java.lang.Error) {
        throw (java.lang.Error) rac$e;
    }
  }

  /** Generated by JML to save pre-values against potential recursive
    * method calls to the method main. */
  private static transient java.util.Stack rac$stack1 = new java.util.Stack();

  /** Generated by JML to save pre-values for the method main. */
  private static void saveTo$rac$stack1() {
    java.lang.Object[] values = new java.lang.Object[1];
    values[0] = new java.lang.Boolean(rac$pre2);
    rac$stack1.push(values);
  }

  /** Generated by JML to restore pre-values for the method main. */
  private static void restoreFrom$rac$stack1() {
    java.lang.Object[] values = (java.lang.Object[])rac$stack1.pop();
    rac$pre2 = ((java.lang.Boolean) values[0]).booleanValue();
  }

  /** Generated by JML to wrap assertion check code to
   * the method main. */
  public static void main(java.lang.String[] args) {
    // skip assertion checks during initialization
    if (!rac$ClassInitialized) {
      internal$main(args);
      return;
    }
    if (!(JMLChecker.isActive(JMLChecker.PRECONDITION))) {
      internal$main(args);
      return;
    }
    // eval old exprs in constraint
    if (JMLChecker.isActive(JMLChecker.CONSTRAINT)) {
      JMLChecker.enter();
      evalOldExprInHC$static();
      JMLChecker.exit();
    }
    // check static invariant
    if (JMLChecker.isActive(JMLChecker.INVARIANT)) {
      JMLChecker.enter();
      checkInv$static("main@pre<File \"src/dk/itu/jmlexamples/binsearch/BinSearch.java\", line 49, character 15>");
      JMLChecker.exit();
    }
    // check precondition
    if (JMLChecker.isActive(JMLChecker.PRECONDITION)) {
      JMLChecker.enter();
      checkPre$main$BinSearch(args);
      JMLChecker.exit();
    }
    boolean rac$ok = true;
    try {
      // execute original method
      internal$main(args);
      // check normal postcondition
      if (JMLChecker.isActive(JMLChecker.POSTCONDITION)) {
        JMLChecker.enter();
        checkPost$main$BinSearch(args,null);
        JMLChecker.exit();
      }
    }
    catch (JMLEntryPreconditionError rac$e) {
      rac$ok = false;
      throw new JMLInternalPreconditionError(rac$e);
    }
    catch (JMLExitNormalPostconditionError rac$e) {
      rac$ok = false;
      throw new JMLInternalNormalPostconditionError(rac$e);
    }
    catch (JMLExitExceptionalPostconditionError rac$e) {
      rac$ok = false;
      throw new JMLInternalExceptionalPostconditionError(rac$e);
    }
    catch (JMLAssertionError rac$e) {
      rac$ok = false;
      throw rac$e;
    }
    catch ( java.lang.Throwable rac$e) {
      try {
        // check exceptional postcondition
        if (JMLChecker.isActive(JMLChecker.POSTCONDITION)) {
          JMLChecker.enter();
          checkXPost$main$BinSearch(args,rac$e);
          JMLChecker.exit();
        }
      }
      catch (JMLAssertionError rac$e1) {
        rac$ok = false;
        throw rac$e1;
      }
    }
    finally {
      if (rac$ok) {
        // check static invariant
        if (JMLChecker.isActive(JMLChecker.INVARIANT)) {
          JMLChecker.enter();
          checkInv$static("main@post<File \"src/dk/itu/jmlexamples/binsearch/BinSearch.java\", line 49, character 15>");
          JMLChecker.exit();
        }
        // check static constraint
        if (JMLChecker.isActive(JMLChecker.CONSTRAINT)) {
          JMLChecker.enter();
          checkHC$static("main@post<File \"src/dk/itu/jmlexamples/binsearch/BinSearch.java\", line 49, character 15>", "main", new java.lang.Class[] { java.lang.String[].class, });
          JMLChecker.exit();
        }
      }
    }
  }

  // Generated by JML
  private static transient boolean rac$pre2;

  /** Generated by JML to make dynamic calls to an assertion
   * check methoda, given its class name (className),
   * method name (name), parameter types (types),
   * and actual arguments (args).
   * If the assertion method returns a boolean value,
   * that value is returned; otherwise, true is returned.
   * An exception thrown by the assertion method is transparently
   * propagated to the caller. */
  private static boolean rac$check(java.lang.String cn, JMLCheckable self,
    java.lang.String name, java.lang.Class types[], java.lang.Object args[]) {
    try {
      java.lang.Class cls = rac$forName(cn);
      java.lang.Object inst = rac$receiver(cn, self);
      java.lang.reflect.Method meth =
        JMLSurrogate.getMethod(cls, name, types);
      java.lang.Object result = meth.invoke(inst, args);
      return (result instanceof java.lang.Boolean) ?
       ((java.lang.Boolean) result).booleanValue() : true;
    }
    catch (java.lang.reflect.InvocationTargetException e) {
      // ok. The invoked method throws an exception, possibly an
      // assertion violation exception. Rethrow it transparently.
      Throwable thr = e.getTargetException();
      if (thr instanceof java.lang.RuntimeException)
         throw (java.lang.RuntimeException) thr;
      else if (thr instanceof java.lang.Error)
         throw (java.lang.Error) thr;
      else
         throw new java.lang.RuntimeException(e.getMessage());
    }
    catch (java.lang.Throwable e) {
       //System.out.println(e.getClass().getName());
       return false;
    }
  }

  /** Generated by JML for caching interface surrogates.
   * It is a mapp from fully qualified interface names
   * to their surrogate objects. */
  public transient java.util.Map rac$surrogates;

  /** Generated by JML to returns the surrogate of
   * the given interface, <code>name</code>. */
  public java.lang.Object rac$getSurrogate(java.lang.String name) {
    if (rac$surrogates == null) {
      rac$surrogates = new java.util.HashMap(37);
    }
    return rac$surrogates.get(name);
  }

  /** Generated by JML to set the surrogate of
   * the given interface, name, to the object obj. */
  public void rac$setSurrogate(java.lang.String name, JMLSurrogate obj) {
    if (rac$surrogates == null) {
      rac$surrogates = new java.util.HashMap(37);
    }
    rac$surrogates.put(name, obj);
  }

  /** Generated by JML to return the actual receiver (possibly
   * a surrogate) for dynamic calls to the class, name. */
  public static java.lang.Object rac$receiver(java.lang.String name, java.lang.Object forObj) {
    if (forObj == null || !name.endsWith("$JmlSurrogate")) {
      return forObj;
    }
    //@ assume forObj instanceof JMLCheckable;
    JMLCheckable cobj = (JMLCheckable) forObj;
    try {
      java.lang.Object surObj = cobj.rac$getSurrogate(name);
      if (surObj == null) {
        java.lang.Class[] types =
          new java.lang.Class[] { JMLCheckable.class };
        java.lang.Class clazz = rac$forName(name);
        java.lang.reflect.Constructor constr =
          clazz.getConstructor(types);
        java.lang.Object[] args = new java.lang.Object[] { cobj };
        surObj = constr.newInstance(args);
        cobj.rac$setSurrogate(name,(JMLSurrogate)surObj);
      }
      return surObj;
    }
    catch (Exception e) {
      java.lang.System.err.println("Internal error in getSurrogate()!");
      //e.printStackTrace();
      System.exit(1);
    }
    return null;
  }

  /** Generated by JML to indicate if an instance completes
     * its construction. */
  private transient boolean rac$dented = false;

  /** Generated by JML to query an instance's construction
    * status. */
  protected boolean rac$dented() {
    return rac$dented;
  }

  /** Generated by JML to return the Class object associated
   * with the class or interface with the given string name. */
  private static java.lang.Class rac$forName(java.lang.String className) {
    java.lang.Object clazz = JMLChecker.classes.get(className);
    if (clazz == JMLChecker.NO_CLASS) {
      throw new java.lang.RuntimeException(className);
    } else if (clazz != null) {
      return (java.lang.Class) clazz;
    }
    try {
      clazz = java.lang.Class.forName(className);
      JMLChecker.classes.put(className, clazz);
      return (java.lang.Class) clazz;
    } catch (java.lang.ClassNotFoundException e) {
      JMLChecker.classes.put(className, JMLChecker.NO_CLASS);
      throw new java.lang.RuntimeException(className);
    }
  }

  /** Generated by JML to indicate the runtime assertion check
   * level of this class; -1 if unspecified. */
  public static transient int rac$level = -1;

  /** Generated by JML to indicate that this type is compiled
   * with runtime assertion check code. */
  public static final boolean rac$RAC_COMPILED = true;

  /** Generated by JML to indicate if the class has completed
     * its initialization. */
  private static transient boolean rac$ClassInitialized = true;

  /** Generated by JML to indicate if an instance has completed
    * its initialization. */
  private transient boolean rac$initialzed = true;

  /** Generated by JML to check the establishment of static
     * invariants. */
  static {
    // cache this class for dynamic calls.
    org.jmlspecs.jmlrac.runtime.JMLChecker.classes.put("dk.itu.jmlexamples.binsearch.BinSearch", dk.itu.jmlexamples.binsearch.BinSearch.class);
    // check static invariant.
    checkInv$static("<clinit>");
  }

}

```




