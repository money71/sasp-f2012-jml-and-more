package dk.itu.openjml.quantifiers;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertEquals;
import junit.framework.Assert;

import org.junit.Test;

/**
 * This test class *runs* the code compiled with the ForAll.java class.
 * - the code is slightly modified because of JUnit requires use of its  
 * own asserts not the build in Java <b>assert something</b>. 
 */
public class Test_ForAllCompiledForRAC {
	
	@Test
	public void testJML$ITU$ForAll1() {
		try{
			JML$ITU$ForAll1.forAll();
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	@Test
	public void testJML$ITU$ForAll2() {
		try{
			JML$ITU$ForAll2.forAll();
		} catch (Exception e){
			Assert.fail();
		}
	}

	@Test
	public void testJML$ITU$ForAll3() {
		try{
			JML$ITU$ForAll3.forAll();
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	@Test
	public void testJML$ITU$ForAll4() {
		try{
			JML$ITU$ForAll4.forAll();
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	@Test
	public void testJML$ITU$ForAll5() {
		try{
			JML$ITU$ForAll5.forAll();
		} catch (AssertionError a){
			assertEquals("java.lang.AssertionError: ", a.toString());
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	@Test
	public void testJML$ITU$ForAll6() {
		try{
			JML$ITU$ForAll6.forAll();
		} catch (Exception e){
			Assert.fail();
		}
	}
	
}


/**
 * s.add("//@ requires (\\forall int i; 0 <= i && i < 10; i < 10);");
 * P, predicate holds always true for this one.
 */
class JML$ITU$ForAll1 {
  
  JML$ITU$ForAll1() {
    super();
  }
  
  public static void forAll() {
    for (int i : dk.itu.openjml.quantifiers.IntervalSet.intersect(dk.itu.openjml.quantifiers.IntervalSet.interval(0, Integer.MAX_VALUE), dk.itu.openjml.quantifiers.IntervalSet.interval(Integer.MIN_VALUE, 10 - 1))) {
      assert i < 10;
      // Repeat for JUNIT: 
      assertTrue(i < 10);
    }
  }
}

/**
 * s.add("//@ requires (\\forall int i; i >= 5 || i < 10; i < 10);");
 * P, predicate holds always true for this one. 
 */
class JML$ITU$ForAll2 {
  
  JML$ITU$ForAll2() {
    super();
  }
  
  public static void forAll() {
    for (int i : dk.itu.openjml.quantifiers.IntervalSet.union(dk.itu.openjml.quantifiers.IntervalSet.interval(5, Integer.MAX_VALUE), dk.itu.openjml.quantifiers.IntervalSet.interval(Integer.MIN_VALUE, 10 - 1))) {
      assert i < 10;
      // Repeat for JUNIT: 
      assertTrue(i < 10);      
    }
  }
}

/**
 * s.add("//@ requires (\\forall int i; i >= 5 || i < 10 && i < 300; i > 0);");
 * P, predicate holds always true for this one.
 */
class JML$ITU$ForAll3 {
  
  JML$ITU$ForAll3() {
    super();
  }
  
  public static void forAll() {
    for (int i : dk.itu.openjml.quantifiers.IntervalSet.union(dk.itu.openjml.quantifiers.IntervalSet.interval(5, Integer.MAX_VALUE), dk.itu.openjml.quantifiers.IntervalSet.intersect(dk.itu.openjml.quantifiers.IntervalSet.interval(Integer.MIN_VALUE, 10 - 1), dk.itu.openjml.quantifiers.IntervalSet.interval(Integer.MIN_VALUE, 300 - 1)))) {
      assert i > 0;
      // Repeat for JUNIT: 
      assertTrue(i > 0);
    }
  }
}

/*
 * //@ requires (\\forall int i; i >= 5 || i < 10 && i < 300 && i != 500; i > 10 )
 */
class JML$ITU$ForAll4 {
  
  JML$ITU$ForAll4() {
    super();
  }
  
  public static void forAll() {
    for (int i : dk.itu.openjml.quantifiers.IntervalSet.union(dk.itu.openjml.quantifiers.IntervalSet.interval(5, Integer.MAX_VALUE), dk.itu.openjml.quantifiers.IntervalSet.intersect(dk.itu.openjml.quantifiers.IntervalSet.intersect(dk.itu.openjml.quantifiers.IntervalSet.interval(Integer.MIN_VALUE, 10 - 1), dk.itu.openjml.quantifiers.IntervalSet.interval(Integer.MIN_VALUE, 300 - 1)), dk.itu.openjml.quantifiers.IntervalSet.interval(500 + 1, 500 - 1)))) {
      assert i > 10;
      // Repeat for JUNIT: 
      assertTrue(i > 10);
    }
  }
}

/*
 * //@ requires (\\forall int i, j, h; 0 <= i && i < 10 && 50 < j && j <= 100; i == (j - 1))
 * P, predicate does NOT hold always true for this one.
 */
class JML$ITU$ForAll5 {
	  
	  JML$ITU$ForAll5() {
	    super();
	  }
	  
	  public static void forAll() {
	    for (int i : dk.itu.openjml.quantifiers.IntervalSet.intersect(dk.itu.openjml.quantifiers.IntervalSet.interval(0, Integer.MAX_VALUE), dk.itu.openjml.quantifiers.IntervalSet.interval(Integer.MIN_VALUE, 10 - 1))) {
	      for (int j : dk.itu.openjml.quantifiers.IntervalSet.intersect(dk.itu.openjml.quantifiers.IntervalSet.interval(50 + 1, Integer.MAX_VALUE), dk.itu.openjml.quantifiers.IntervalSet.interval(Integer.MIN_VALUE, 100))) {
	        for (int h : dk.itu.openjml.quantifiers.IntervalSet.interval(Integer.MIN_VALUE, Integer.MAX_VALUE)) {
	          assert i == (j - 1);
	          // Repeat for JUNIT: 
	          assertTrue(i == (j - 1));
	        }
	      }
	    }
	  }
	}


/*
 * //@ requires (\\forall int i; -100 < i && i < 0 || 0 < i && i < 100; i != 0)
 * P, predicate holds always true for this one.
 */
class JML$ITU$ForAll6 {
  
  JML$ITU$ForAll6() {
    super();
  }
  
  public static void forAll() {
    for (int i : dk.itu.openjml.quantifiers.IntervalSet.union(dk.itu.openjml.quantifiers.IntervalSet.intersect(dk.itu.openjml.quantifiers.IntervalSet.interval(-100 + 1, Integer.MAX_VALUE), dk.itu.openjml.quantifiers.IntervalSet.interval(Integer.MIN_VALUE, 0 - 1)), dk.itu.openjml.quantifiers.IntervalSet.intersect(dk.itu.openjml.quantifiers.IntervalSet.interval(0 + 1, Integer.MAX_VALUE), dk.itu.openjml.quantifiers.IntervalSet.interval(Integer.MIN_VALUE, 100 - 1)))) {
      assert i != 0;
      // Repeat for JUNIT: 
      assertTrue(i != 0);
    }
  }
}
