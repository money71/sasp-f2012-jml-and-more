package dk.itu.openjml.quantifiers;

import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr; 
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import dk.itu.openjml.quantifiers.QRange;

public class Test_QRange extends Test_ForAll {

	@Before
	public void setUp() throws Exception {
		super.setUp();
	}

	@Test
	public void testCompute() {
		for(JmlQuantifiedExpr t: qExprsAst) {
			System.out.println(t);
			String p = "";			
			try{
				p = QRange.compute(t.range, "i").translate();
			} catch (Exception e){
				Assert.fail(e.toString());
			}
			System.out.println(p);
		}
	}
	
}
