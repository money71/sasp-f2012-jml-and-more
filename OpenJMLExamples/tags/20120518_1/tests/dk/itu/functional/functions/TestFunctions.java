package dk.itu.functional.functions;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

/**
 * 
 * Based upon xxx - add ref to functional java book
 *
 */
public class TestFunctions {

	static boolean called = false;

	@Before
	public void setup() {
		called = false;
	}

	// org example
	private Boolean invokeCallback1(Function1<String, Boolean> f) {
		return f.apply("hello!");
	}

	@Test
	public void function1TakesOneArgumentAndReturnsAValue() {
		called = invokeCallback1(new Function1<String, Boolean>() {
			public Boolean apply(String message) {
				return true;
			}
		}).booleanValue();
		assertTrue(called);
	}

	// modified example lets go from bool to string
	private String invokeCallback2(Function1<Boolean, String> f) {
		return f.apply(true);
	}

	@Test
	public void function1TakesOneArgumentAndReturnsAValueBoolToString() {
		String s = invokeCallback2(new Function1<Boolean, String>() {
			public String apply(Boolean a) {
				if (a)
					return "I'm true";
				return "I'm false";
			}
		});
		assertTrue(s instanceof String);
		assertEquals("I'm true", s);
	}
	
	
	
	// i'm a bit confused with the invoke call setup (have to get it with a hammer) 
	// - main while lets take a naive approach:
	@Test
	public void function1TakesOneArgumentAndReturnsAValueBoolToString2() {
		

		Function1<Boolean, String> f = new Function1<Boolean, String>() {
			public String apply(Boolean a) {
				if (a)
					return "I'm true";
				return "I'm false";
			}
		};
		
		String expected1 = "I'm true";
		assertEquals(expected1, f.apply(true));
		
		String expected2 = "I'm false";
		assertEquals(expected2, f.apply(false));
		
	}	
	

	// org example:
	private Object invokeCallback1ConvariantReturn(
			Function1<String, ? extends Object> f) {
		return f.apply("hello!");
	}

	@Test
	public void functionsWithCovariantReturnssAreValid() {
		Object result = invokeCallback1ConvariantReturn(new Function1<String, Object>() {
			public Object apply(String message) {
				return true;
			}
		});
		assertTrue(result instanceof Boolean);
		called = ((Boolean) result).booleanValue();
		assertTrue(called);
	}

}
