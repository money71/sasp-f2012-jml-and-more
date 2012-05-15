package dk.itu.openjml.test;

import static org.junit.Assert.*;

import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import dk.itu.openjml.forall.ForAllNaive;
import dk.itu.openjml.quantifiers.QRange;

public class Test_QRange extends Test_ForAllNaive {

	@Before
	public void setUp() throws Exception {
		super.setUp();
	}

	@Test
	public void testCompute() {
		for(JmlQuantifiedExpr t: qExprsAst) {
			String p = "";			
			try{
				p = QRange.compute(t.range, "i").translate();
			} catch (Exception e){
				Assert.fail(e.toString());
			}
			System.out.println(p);
		}
	}
	
	public void testGenerateForAll(){
		// No need to check this today
	}
	
	public void testAssertForAll(){
		// No need to check this today
	}
}
