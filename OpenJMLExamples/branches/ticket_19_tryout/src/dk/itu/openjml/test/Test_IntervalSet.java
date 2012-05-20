package dk.itu.openjml.test;

import static org.junit.Assert.*;

import java.util.Iterator;

import junit.framework.Assert;

import org.junit.Before;
import org.junit.Test;

import dk.itu.openjml.range.IntervalSet;


/**
 * 
 * Test class for the IntervalSet
 * 
 * Keep the specific min /max values in <b>fresh</b> mind: 
 * Min value: -2147483648
 * Max value: 2147483647
 *
 */
public class Test_IntervalSet {
	
	@Before
	public void setUp() throws Exception {
	}
	
	
	@Test
	public void testIntervalSetBasic() {
		IntervalSet i = IntervalSet.interval(0, 10);		
		assertNotNull(i);
	}

	@Test
	public void testIntervalSetBasicForEach() {
		IntervalSet i = IntervalSet.interval(0, 10);
		int count = 0;
		for(int n: i){
			assertNotNull(n);
			count++;
		}
		assertEquals(11, count);
	}
	
	@Test
	public void testIntervalSetBasicIterator() {
		IntervalSet i = IntervalSet.interval(0, 10);
		int count = 0;
		Iterator<Integer> ite = i.iterator();
		while(ite.hasNext()){
			assertNotNull(ite.next());
			count++;
		}
		assertEquals(11, count);
	}
	
	
//	@Test
//	public void testUnionGap() {
//		IntervalSet u = IntervalSet.union(IntervalSet.interval(0, 10), 
//										  IntervalSet.interval(12, 20));
//		try{
//			String su = "Union: ";
//			for(int n: u){
//				su += n + "; ";
//				assertTrue(0 <= n && n <= 10 || 12 <= n && n <= 20);
//			}
//			System.out.println(su);
//		} catch (Exception e){
//			Assert.fail();
//		}
//	}
//	
//	@Test
//	public void testIntersection() {
//		IntervalSet i = IntervalSet.intersect(IntervalSet.interval(0, 11), 
//				                              IntervalSet.interval(5, 15));
//		try{
//			String si = "Intersection: ";
//			for(int n: i){
//				si += n + "; ";
//				assertTrue(0 <= n && n <= 10 && 5 <= n && n <= 15);
//			}
//		System.out.println(si);
//		} catch (Exception e){
//			Assert.fail();
//		}
//	}
//	
//	@Test
//	public void testIntersectedUnion() {
//		IntervalSet u = IntervalSet.union(IntervalSet.interval(0, 11), 
//				                          IntervalSet.interval(20, 31));
//		IntervalSet iu = IntervalSet.intersect(u, IntervalSet.interval(5, 26));
//		try{
//			String siu = "Intersected union: ";
//			for(int n: iu){
//				siu += n + "; ";
//				assertTrue(0 <= n && n <= 10 || 20 <= n && n <= 30 && 5 <= n && n <= 25);
//			}	
//			System.out.println(siu);
//		} catch (Exception e){
//			Assert.fail();
//		}
//	}
//	
//	@Test
//	public void testUnitedIntersection() {
//		IntervalSet i = IntervalSet.intersect(IntervalSet.interval(0, 101), IntervalSet.interval(50, 151));
//		IntervalSet ui = IntervalSet.union(i, IntervalSet.interval(40, 61));
//		try{				
//			String sui = "United intersection: ";
//			for(int n: ui){
//				sui += n + "; ";
//				assertTrue(0 <= n && n <= 100 && 50 <= n && n <= 150 || 40 <= n && n <= 60);
//			}
//			System.out.println(sui);
//		} catch (Exception e){
//			Assert.fail();
//		}
//	}
//	
//	@Test
//	public void testNotInside() {
//		IntervalSet ni = IntervalSet.union(IntervalSet.interval(0, 101), IntervalSet.interval(51, 50));
//		try{				
//			String sni = "Union without 50: ";
//			for(int n: ni){
//				sni += n + "; ";
//				assertTrue(0 <= n && n <= 100 && n != 50);
//			}
//			System.out.println(sni);
//		} catch (Exception e){
//			Assert.fail();
//		}
//	}	

	
	
	
	
	/**
	 * (2147483644, 2147483645) union (2147483646, 2147483647) => 
	 * (2147483644, 2147483645, 2147483646, 2147483647)
	 */	
	@Test
	public void testUnionMaxValue() {
		IntervalSet u = IntervalSet.union(
							IntervalSet.interval(Integer.MAX_VALUE-3, Integer.MAX_VALUE-2), 
							IntervalSet.interval(Integer.MAX_VALUE-1, Integer.MAX_VALUE)
							);
		try{
			String su = "Union: ";
			int count = 0;
			for(int n: u){
				su += n + "; ";
				assertTrue(Integer.MAX_VALUE-3 <= n && n <= Integer.MAX_VALUE);
				count++;
			}
			System.out.println(su);
			assertEquals(4, count);			
		} catch (Exception e){
			Assert.fail();
		}
	}

	
	/**
	 * (2147483645, 2147483647) union (2147483645, 2147483647) => 
	 * (2147483645, 2147483646, 2147483647)
	 */	
	@Test
	public void testUnionMaxValueSameIntervals() {
		IntervalSet u = IntervalSet.union(
							IntervalSet.interval(Integer.MAX_VALUE-2, Integer.MAX_VALUE), 
							IntervalSet.interval(Integer.MAX_VALUE-2, Integer.MAX_VALUE)
							);
		try{
			String su = "Union: ";
			int count = 0;
			for(int n: u){
				su += n + "; ";
				assertTrue(Integer.MAX_VALUE-2 <= n && n <= Integer.MAX_VALUE);
				count++;
			}
			System.out.println(su);
			assertEquals(3, count);			
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	/** 
	 * (-2147483648, -2147483647) union (-2147483646, -2147483645) => 
	 * (-2147483648, -2147483647, -2147483646, -2147483645)
	 */	
	@Test
	public void testUnionMinValue() {
		IntervalSet u = IntervalSet.union(
							IntervalSet.interval(Integer.MIN_VALUE, Integer.MIN_VALUE+1), 
							IntervalSet.interval(Integer.MIN_VALUE+2, Integer.MIN_VALUE+3)
							);
		try{
			String su = "Union: ";
			int count = 0;
			for(int n: u){
				System.out.println(n);
				su += n + "; ";
				assertTrue(Integer.MIN_VALUE <= n && n <= Integer.MIN_VALUE+3);
				count++;
			}
			System.out.println(su);
			assertEquals(4, count);			
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	/** 
	 * (-2147483648, -2147483646) union (-2147483648, -2147483646) => 
	 * (-2147483648, -2147483647, -2147483646)
	 */	
	//@Test
	public void testUnionMinValueSameIntervals() {
		IntervalSet u = IntervalSet.union(
							IntervalSet.interval(Integer.MIN_VALUE, Integer.MIN_VALUE+2), 
							IntervalSet.interval(Integer.MIN_VALUE, Integer.MIN_VALUE+2)
							);
		try{
			String su = "Union: ";
			int count = 0;
			for(int n: u){
				su += n + "; ";
				assertTrue(Integer.MIN_VALUE <= n && n <= Integer.MIN_VALUE+2);
				count++;
			}
			System.out.println(su);
			assertEquals(3, count);			
		} catch (Exception e){
			Assert.fail();
		}
	}
	
}