package dk.itu.mathmodelstest.set;

import java.util.EnumSet;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.SortedSet;
import java.util.TreeSet;

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
		
		
//		System.out.println("============s============");
//		System.out.println(s2);
		
	
		// union 				
						
		// intersection
		
		// set difference
		
	}
	
	
	
	/*
	 * TreeSet has O(log n) one basic operations
	 * like add | remove | contains -
	 * 
	 * - opposite to HashSet that have O(1) - there is a niece overview 
	 * of that in "Java Precisely (2nd edition) by Peter Sestoft p. 108".
	 */
	@Test
	public void testBasicSortedSet() 
	{
		
		// TreeSet implements SortedSet that implements 
		// Set that implements collection   
		SortedSet<Integer> s = new TreeSet<Integer>();
		s.add(10);
		s.add(2);
		s.add(3);
		s.add(9);
		s.add(9);

//		traverse(s);
				
		Object[] expected = {2, 3, 9, 10};
		Object[] result = s.toArray();
		Assert.assertArrayEquals(expected, result);

		
		// union = addAll()
		SortedSet<Integer> s2 = new TreeSet<Integer>();
		s2.add(1);
		s2.add(2);
		s2.add(2);
		
		s.addAll(s2);
		Object[] expected2 = {1, 2, 3, 9, 10};
		Object[] result2 = s.toArray();
		Assert.assertArrayEquals(expected2, result2);		
		
		// intersection = retainAll()
		SortedSet<Integer> s3 = new TreeSet<Integer>();
		s3.add(3);
		s3.add(9);

		s3.retainAll(s);
		Object[] expected3 = {3, 9};
		Object[] result3 = s3.toArray();
		Assert.assertArrayEquals(expected3, result3);		
		
		// set difference = removeAll() 
		SortedSet<Integer> s4 = new TreeSet<Integer>();
		s4.add(1);
		s4.add(3);
		s4.add(9);
		s4.add(13);		
		
		s4.removeAll(s3);
		Object[] expected4 = {1, 13};
		Object[] result4 = s4.toArray();
		Assert.assertArrayEquals(expected4, result4);
				
		System.out.println("============s============");
		System.out.println(s4);
		

	}
	
	
}
