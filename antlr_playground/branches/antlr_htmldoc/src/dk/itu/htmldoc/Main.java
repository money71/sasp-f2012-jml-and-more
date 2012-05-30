package dk.itu.htmldoc;


import java.io.IOException;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
import org.antlr.runtime.TokenRewriteStream;
import org.antlr.runtime.tree.CommonTree;
import org.antlr.runtime.tree.CommonTreeAdaptor;
import org.antlr.runtime.tree.TreeAdaptor;


/**
 * 
 * Based upon the tutorial:
 * http://www.antlr.org/wiki/display/ANTLR3/Interfacing+AST+with+Java
 *
 */
public class Main {
	
	
	static final CommonTreeAdaptor adaptor = new CommonTreeAdaptor() {
		public Object create(Token payload) {
			return new CommonTree(payload);
			/* prints:
DOC
      TITLE
         foo title
      BODY
         fooo body

			 */
			
			//return new HtmlAST(payload);
			/* prints:
DOC
      TITLETITLE
         foo titlefoo title
      BODYBODY
         fooo bodyfooo body
			 * */
		}
	};
	

	static final void printTree(CommonTree t, int indent) {
		if ( t != null ) {
			StringBuffer sb = new StringBuffer(indent);
			
			if (t.getParent() == null){
				System.out.println(sb.toString() + t.getText().toString());	
			}
			for ( int i = 0; i < indent; i++ )
				sb = sb.append("   ");
			for ( int i = 0; i < t.getChildCount(); i++ ) {
				System.out.println(sb.toString() + t.getChild(i).toString());
				printTree((CommonTree)t.getChild(i), indent+1);
			}
		}
	}
	
	
	/**
	 * @param args
	 * @throws IOException 
	 * @throws RecognitionException 
	 */
	public static void main(String[] args) throws IOException, RecognitionException {
		// TODO Auto-generated method stub

		ANTLRFileStream fs = new ANTLRFileStream("src/dk/itu/htmldoc/test.html");
		HtmlDocLexer lex = new HtmlDocLexer(fs);
		TokenRewriteStream tokens = new TokenRewriteStream(lex);
		HtmlDocParser grammar = new HtmlDocParser(tokens);

		// hook things together
		grammar.setTreeAdaptor(adaptor);
		HtmlDocParser.html_doc_return ret = grammar.html_doc();
		CommonTree tree = (CommonTree)ret.getTree();

		
//		System.out.println(tree);
		printTree(tree, 2);
		
		
		
	}

}
