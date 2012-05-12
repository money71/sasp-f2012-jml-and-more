package dk.itu.mathmodelstest.quantifiers;

import java.io.File;
import java.io.IOException;
import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.junit.Assert;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import com.sun.tools.javac.tree.JCTree;

import dk.itu.mathmodels.quantifiers.ForAll;


public class TestForAll {
	
	
	
	@Test
	public void testForAll() 
	{
	
		Assert.assertTrue(ForAll.forall());

	}	

	@Test
	public void testForAllBreak() 
	{
	
		Assert.assertTrue(ForAll.forallBreak());

	}
	
	
	
	
}
