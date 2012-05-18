package dk.itu.openjml.rangeextended;

import static dk.itu.openjml.rangeextended.collection.List; 
import static dk.itu.openjml.rangeextended.collection.Array;
import static dk.itu.openjml.rangeextended.collection.Set;
import static dk.itu.openjml.rangeextended.collection.Range;
import static dk.itu.openjml.rangeextended.collection.Date;


import java.lang.reflect.Array;
import java.util.List;
import java.util.Set;
import java.util.HashSet;

import org.junit.Assert;
import org.junit.Test;

public class TestCollection {
	
	
	@Test
	public void testCollectionInstantiationForListStringInteger()
	{
		
		List<String> slist = List( "a", "b", "c" );

		for( String elem : slist ){
			Assert.assertTrue(slist.contains(elem));
		}

		List<Integer> iList = List( 1, 2, 3 );
		
		for( Integer elem : iList ){
			Assert.assertTrue(iList.contains(elem));
		}
		
	}

	
	@Test
	public void testCollectionInstantiationForArrayStringInteger()
	{
		
		String[] sArray = Array( "a", "b", "c" );
		
		for( String elem : sArray ){
			// Assert.assertTrue(sArray.contains(elem));
			// FIXME: sArray has no contains() - find another way to set an assert
			System.out.print(elem);
		}

		Integer[] iArray = Array( 1, 2, 3 );		
		for( Integer elem : iArray ){
			// Assert.assertTrue(iArray.contains(elem));
			// FIXME: iArray has no contains() - find another way to set an assert
			System.out.print(elem);
		}

	}	
	
	@Test
	public void testCollectionInstantiationForSetStringInteger()
	{
				
		Set<String> s = Set("a", "b", "c");

		for( String elem : s ){
			Assert.assertTrue(s.contains(elem));
		}

	}
	

	@Test
	public void testCollectionInstantiationForRangeStringInteger()
	{

		// int
		Assert.assertTrue( Range( 11, 22 ).contains( 17 ) );
		Assert.assertFalse( Range( 11, 22 ).contains( 28 ) );
	
		
		// FIXME: look into this one not working yet
		// date
//		Assert.assertTrue( Range( Date( "11.04.2005" ), Date( "27.09.2007" ) ).contains( Date( "23.07.2006" ) ) );

		// char - ?
		Assert.assertTrue( Range( 'a', 'z' ).contains( 'q' ) );
		// string
		Assert.assertTrue( Range( "a", "z" ).contains( "q" ) );

	}

	
	
	
}
