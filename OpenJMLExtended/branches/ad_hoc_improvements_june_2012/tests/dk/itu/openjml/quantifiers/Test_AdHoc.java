package dk.itu.openjml.quantifiers;

import org.junit.Assert;
import org.junit.Test;

/**
 * This test class requires no launch configuration
 * and is intended for small ad hoc tests
 */
public class Test_AdHoc {
	
	/*
	 * Simulate the getOperator in QRange:
	 * "<= dk.itu.openjml.quantifiers.Test_ForAll.array.length"
	 * is currently replaced into:
	 * "<=dk.tu.openjml.quantfers.Test_ForAll.array.length"
	 * which with fresh eyes also is correct and shows the limits of the 
	 * getOperator implementation.
	 */
	@Test
	public void testQRangeGetOperatorStringReplaceTicket_15_31() {	
		
		final String s = "i <= dk.itu.openjml.quantifiers.Test_ForAll.array.length";
		final String lhs = "i";
		final String rhs = "dk.itu.openjml.quantifiers.Test_ForAll.array.length";
		final String result = s.replace(lhs, "").replace(rhs, "").replace(" ", "");
		final String expected = "<=dk.tu.openjml.quantfers.Test_ForAll.array.length"; 
		
		Assert.assertEquals(expected, result);
	
	}

	
	/*
	 * Quick shoot but it wouldn't work to change getOperator into roughly something like:
	 * 
	 * <code>
	 * if (op.contains(GEQ)) { 
	 * 	 return GEQ;
	 * } else if (op.contains(LEQ)) {
	 *   return LEQ;
	 * } else if (op.contains(LT)) {
	 *   return LT;
	 * } else if (op.contains(GT)) {
	 *  return GT;
	 * }
	 * </code> 
	 * 
	 * - because we might have an even bigger expression previously with multiple expressions:
	 * "0 < i && i <= dk.itu.openjml.quantifiers.Test_ForAll.array.length" 
	 * 
	 * - even with out dk.itu.openjml.quantifiers.Test_ForAll (needed for the OpenJML pretty print)
	 * its possible with further problems think another var name <b>a</b>:
	 * 
	 * "0 < a && a <= array.length" suddenly we have "<= rry.length"
	 * and would get an operator back as  "<=rry.length"
	 * 
	 * - all this really have to be done within the JML so e.getOperator() not
	 * always return null - though we might have misunderstood something on the OpenJML side.
	 * 
	 */
	@Test
	public void testQRangeGetOperatorRegExTicket_15_31() {	
		
		final String s = "i <= dk.itu.openjml.quantifiers.Test_ForAll.array.length";
		final String LEQ = "<=";		
		Assert.assertTrue(s.contains(LEQ));
		// match exact string:
		// Assert.assertTrue(s.matches(LEQ)); 
		// Niece (as all ways) tutorial on java regex: http://goo.gl/gvnYF 
		
	}
	
}
