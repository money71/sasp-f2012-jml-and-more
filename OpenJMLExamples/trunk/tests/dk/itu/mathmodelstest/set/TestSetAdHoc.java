package dk.itu.mathmodelstest.set;

import java.util.EnumSet;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.SortedSet;

import org.junit.Assert;
import org.junit.Test;


public class TestSetAdHoc {

	
	/**
	 * http://docs.oracle.com/javase/6/docs/api/java/util/EnumSet.html
	 */
	@Test
	public void testBasicHashSet() 
	{
		
		HashSet<Integer> s = new HashSet<Integer>();
		s.add(1);
		s.add(2);		
		Assert.assertFalse(s.isEmpty());
		
		HashSet<Integer> s2 = new HashSet<Integer>();
		s2.addAll(s);
		s2.add(3);
		Assert.assertEquals(3, s2.size());

	}

	@Test
	public void testLinkedHashSet() 
	{	
		// LinkedHashSet has better ordering features (the order added)
	
		LinkedHashSet<Integer> s = new LinkedHashSet<Integer>();
		s.add(10);
		s.add(2);
		s.add(3);
		s.add(9);
		s.add(9);
		
		Object[] a = {10, 2, 3, 9};
		Object[] b = s.toArray();
		Assert.assertArrayEquals(a, b);
		

		LinkedHashSet<Integer> s2 = new LinkedHashSet<Integer>();
		s2.add(2);
		s2.add(3);
		s2.add(3);		
		s2.add(11);
		
		
		System.out.println("============s============");
		System.out.println(s2);
		
	
		// union 				
						
		// intersection
		
		// set difference
		
	}
	
	
//	@Test
//	public void testBasicSortedSet() 
//	{
//		
//		SortedSet<Integer> s = new SortedSet<Integer>();
//		
////		SortedSet<Integer> sub = s.subSet(low, high+"\0");
//	}
//	
//	
	
	
	
	
	
	
	
}
