package dk.itu.openjml.test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import dk.itu.openjml.range.IntervalSet;

public class Test_IntervalSet {
	
	@Before
	public void setUp() throws Exception {
	}

	@Test
	public void test() {
		IntervalSet p = IntervalSet.union(IntervalSet.interval(0, 9), IntervalSet.interval(11, 20));
		
		String r = "";
		while(p.hasNext()){
			r += p.next() + ", ";
		}
		
		System.out.println(r);
	}

}
