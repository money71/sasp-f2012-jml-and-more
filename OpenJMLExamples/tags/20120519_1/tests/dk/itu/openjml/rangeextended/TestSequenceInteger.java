package dk.itu.openjml.rangeextended;

import dk.itu.openjml.rangeextended.SequenceInteger;

import org.junit.Assert;
import org.junit.Test;

public class TestSequenceInteger {
	
	@Test
	public void testIntergerSequenceBasic()
	{
		SequenceInteger s = new SequenceInteger(3);
		
		Assert.assertEquals(new Integer(4), s.next().value());
		Assert.assertEquals(new Integer(2), s.previous().value());
		
	}	

	/**
	 * min =-2147483648
	 * max = 2147483647
	 */
	@Test
	public void testIntergerSequenceBasicOutSideRange()
	{
		SequenceInteger sMax = new SequenceInteger(Integer.MAX_VALUE);
		 
		Assert.assertEquals(new Integer(Integer.MIN_VALUE), sMax.next().value());
		Assert.assertEquals(new Integer(Integer.MAX_VALUE - 1), sMax.previous().value());
		
		
		SequenceInteger sMin = new SequenceInteger(Integer.MIN_VALUE);
		
		
		Assert.assertEquals(new Integer(Integer.MIN_VALUE + 1), sMin.next().value());
		Assert.assertEquals(new Integer(Integer.MAX_VALUE), sMin.previous().value());

		
	}	
	
	
}
