package dk.itu.openjml.test;

import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import dk.itu.openjml.forall.ForAll;

public class Test_ForAll extends Test_ForAllNaive {

	@Before
	public void setUp() throws Exception {
		super.setUp();
	}

	@Test
	public void testForAll() {
		for(JmlQuantifiedExpr t: qExprsAst) {
			System.out.println(t);
			ForAll p;			
			try{
				p = new ForAll(t);
				System.out.println(p.translate());
			} catch (Exception e){
				Assert.fail(e.toString());
			}
		}
	}

	@Override
	public void testGenerateForAll() {
	}

	@Override
	public void testAssertForAll() {
	}
	
	

}
