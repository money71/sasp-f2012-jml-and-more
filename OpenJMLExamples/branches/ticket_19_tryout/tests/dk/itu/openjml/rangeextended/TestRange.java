package dk.itu.openjml.rangeextended;

import java.util.ArrayList;   
import java.util.LinkedHashSet;

import org.junit.Assert;
import org.junit.Test;

import dk.itu.openjml.rangeextended.Range;
import static dk.itu.openjml.rangeextended.collection.Range;

public class TestRange {

	@Test
	public void testRangeIntegersBasic() 
	{
		
		Assert.assertTrue( new Range( 11, 22 ).contains( 17 ) );
		Assert.assertFalse( new Range( 11, 22 ).contains( 28 ) );

		Assert.assertTrue( new Range( 100, Integer.MAX_VALUE ).contains( 200 ) );
		Assert.assertFalse( new Range( 100, Integer.MAX_VALUE ).contains( 28 ) );
		
		Assert.assertTrue( new Range( Integer.MIN_VALUE, 0  ).contains( -200 ) );
		Assert.assertFalse( new Range( Integer.MIN_VALUE, 0 ).contains( 1 ) );
		
	}

	// @Test
	public void testRangeByteBasic() 
	{
		// TODO
	}

	// @Test
	public void testRangeCharBasic() 
	{
		// TODO
	}

	
	/*
		Now we can do something like:
		for( int number : Range( 11, 22 ) ){
			if( number%2 == 0 ) 
				System.out.println( number + " is even" );
			else
				System.out.println( number + " is odd" );
		}
	 */
	@Test
	public void testRangeIterator() 
	{
		int count = 11;
		// just a quick naive test
		for( int number : Range( 11, 22 ) ){
			Assert.assertEquals(count, number);			
			count++;
		}
		
	}	
	
}