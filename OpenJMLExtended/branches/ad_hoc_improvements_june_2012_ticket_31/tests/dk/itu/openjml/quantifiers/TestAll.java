package dk.itu.openjml.quantifiers;

import org.junit.runner.RunWith;  
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses( {  
	Test_ForAll.class,
	Test_IntervalSet.class,
	Test_QRange.class,
	Test_ForAllCompiledForRAC.class
} )

/**
 * This test case requires to be run with the launch configuration:
 * - TestAllOpenJMLExtended.launch
 */
public class TestAll {

}

