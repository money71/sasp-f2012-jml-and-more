package dk.itu.openjml.rangetest;

import java.util.ArrayList;
import java.util.LinkedHashSet;

import org.junit.Assert;
import org.junit.Test;

import dk.itu.openjml.range.Range;

public class TestRange {

	@Test
	public void testRangeBasic() 
	{
		
		Assert.assertTrue( new Range( 11, 22 ).contains( 17 ) );
		Assert.assertFalse( new Range( 11, 22 ).contains( 28 ) );

		Assert.assertTrue( new Range( 100, Integer.MAX_VALUE ).contains( 200 ) );
		Assert.assertFalse( new Range( 100, Integer.MAX_VALUE ).contains( 28 ) );
		
		Assert.assertTrue( new Range( Integer.MIN_VALUE, 0  ).contains( -200 ) );
		Assert.assertFalse( new Range( Integer.MIN_VALUE, 0 ).contains( 1 ) );
		
	}

	
	@Test
	public void testRangeCompute() 
	{
		Range r = new Range( 11, 22 );
				
		LinkedHashSet<Integer> s = r.compute();
		
		Object[] a = {11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22};
		Object[] b = s.toArray();
		Assert.assertArrayEquals(a, b);
				
		Assert.assertEquals(12, s.size());
		
	}
	
	
	
	//@Test
	public void testRangeUnion() 
	{
		Range r1 = new Range( 11, 22 );
		Range r2 = new Range( 18, 40 );
		
		Range r3 = r1.union(r2);
		
		Assert.assertTrue( r3.contains( 11 ) );
		Assert.assertTrue( r3.contains( 40 ) );
		
	}
	
	
}
