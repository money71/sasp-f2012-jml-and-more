// $ANTLR 3.4 /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g 2012-05-30 22:11:28

  package dk.itu.htmldoc;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

import org.antlr.runtime.tree.*;


@SuppressWarnings({"all", "warnings", "unchecked"})
public class HtmlDocParser extends Parser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "BODY", "DOC", "TEXT", "TITLE", "'</body>'", "'</html>'", "'</title>'", "'<body>'", "'<html>'", "'<title>'"
    };

    public static final int EOF=-1;
    public static final int T__8=8;
    public static final int T__9=9;
    public static final int T__10=10;
    public static final int T__11=11;
    public static final int T__12=12;
    public static final int T__13=13;
    public static final int BODY=4;
    public static final int DOC=5;
    public static final int TEXT=6;
    public static final int TITLE=7;

    // delegates
    public Parser[] getDelegates() {
        return new Parser[] {};
    }

    // delegators


    public HtmlDocParser(TokenStream input) {
        this(input, new RecognizerSharedState());
    }
    public HtmlDocParser(TokenStream input, RecognizerSharedState state) {
        super(input, state);
    }

protected TreeAdaptor adaptor = new CommonTreeAdaptor();

public void setTreeAdaptor(TreeAdaptor adaptor) {
    this.adaptor = adaptor;
}
public TreeAdaptor getTreeAdaptor() {
    return adaptor;
}
    public String[] getTokenNames() { return HtmlDocParser.tokenNames; }
    public String getGrammarFileName() { return "/Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g"; }


    public static class html_doc_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "html_doc"
    // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:17:1: html_doc : '<html>' html_header html_body '</html>' -> ^( 'doc' html_header html_body ) ;
    public final HtmlDocParser.html_doc_return html_doc() throws RecognitionException {
        HtmlDocParser.html_doc_return retval = new HtmlDocParser.html_doc_return();
        retval.start = input.LT(1);


        Object root_0 = null;

        Token string_literal1=null;
        Token string_literal4=null;
        HtmlDocParser.html_header_return html_header2 =null;

        HtmlDocParser.html_body_return html_body3 =null;


        Object string_literal1_tree=null;
        Object string_literal4_tree=null;
        RewriteRuleTokenStream stream_9=new RewriteRuleTokenStream(adaptor,"token 9");
        RewriteRuleTokenStream stream_12=new RewriteRuleTokenStream(adaptor,"token 12");
        RewriteRuleSubtreeStream stream_html_body=new RewriteRuleSubtreeStream(adaptor,"rule html_body");
        RewriteRuleSubtreeStream stream_html_header=new RewriteRuleSubtreeStream(adaptor,"rule html_header");
        try {
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:18:2: ( '<html>' html_header html_body '</html>' -> ^( 'doc' html_header html_body ) )
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:18:4: '<html>' html_header html_body '</html>'
            {
            string_literal1=(Token)match(input,12,FOLLOW_12_in_html_doc57);  
            stream_12.add(string_literal1);


            pushFollow(FOLLOW_html_header_in_html_doc59);
            html_header2=html_header();

            state._fsp--;

            stream_html_header.add(html_header2.getTree());

            pushFollow(FOLLOW_html_body_in_html_doc61);
            html_body3=html_body();

            state._fsp--;

            stream_html_body.add(html_body3.getTree());

            string_literal4=(Token)match(input,9,FOLLOW_9_in_html_doc63);  
            stream_9.add(string_literal4);


            // AST REWRITE
            // elements: html_body, DOC, html_header
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Object)adaptor.nil();
            // 18:45: -> ^( 'doc' html_header html_body )
            {
                // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:18:48: ^( 'doc' html_header html_body )
                {
                Object root_1 = (Object)adaptor.nil();
                root_1 = (Object)adaptor.becomeRoot(
                (Object)adaptor.create(DOC, "DOC")
                , root_1);

                adaptor.addChild(root_1, stream_html_header.nextTree());

                adaptor.addChild(root_1, stream_html_body.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "html_doc"


    public static class html_header_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "html_header"
    // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:20:1: html_header : '<title>' TEXT '</title>' -> ^( 'title' TEXT ) ;
    public final HtmlDocParser.html_header_return html_header() throws RecognitionException {
        HtmlDocParser.html_header_return retval = new HtmlDocParser.html_header_return();
        retval.start = input.LT(1);


        Object root_0 = null;

        Token string_literal5=null;
        Token TEXT6=null;
        Token string_literal7=null;

        Object string_literal5_tree=null;
        Object TEXT6_tree=null;
        Object string_literal7_tree=null;
        RewriteRuleTokenStream stream_10=new RewriteRuleTokenStream(adaptor,"token 10");
        RewriteRuleTokenStream stream_TEXT=new RewriteRuleTokenStream(adaptor,"token TEXT");
        RewriteRuleTokenStream stream_13=new RewriteRuleTokenStream(adaptor,"token 13");

        try {
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:21:2: ( '<title>' TEXT '</title>' -> ^( 'title' TEXT ) )
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:21:4: '<title>' TEXT '</title>'
            {
            string_literal5=(Token)match(input,13,FOLLOW_13_in_html_header82);  
            stream_13.add(string_literal5);


            TEXT6=(Token)match(input,TEXT,FOLLOW_TEXT_in_html_header84);  
            stream_TEXT.add(TEXT6);


            string_literal7=(Token)match(input,10,FOLLOW_10_in_html_header86);  
            stream_10.add(string_literal7);


            // AST REWRITE
            // elements: TEXT, TITLE
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Object)adaptor.nil();
            // 21:30: -> ^( 'title' TEXT )
            {
                // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:21:33: ^( 'title' TEXT )
                {
                Object root_1 = (Object)adaptor.nil();
                root_1 = (Object)adaptor.becomeRoot(
                (Object)adaptor.create(TITLE, "TITLE")
                , root_1);

                adaptor.addChild(root_1, 
                stream_TEXT.nextNode()
                );

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "html_header"


    public static class html_body_return extends ParserRuleReturnScope {
        Object tree;
        public Object getTree() { return tree; }
    };


    // $ANTLR start "html_body"
    // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:23:1: html_body : '<body>' TEXT '</body>' -> ^( 'body' TEXT ) ;
    public final HtmlDocParser.html_body_return html_body() throws RecognitionException {
        HtmlDocParser.html_body_return retval = new HtmlDocParser.html_body_return();
        retval.start = input.LT(1);


        Object root_0 = null;

        Token string_literal8=null;
        Token TEXT9=null;
        Token string_literal10=null;

        Object string_literal8_tree=null;
        Object TEXT9_tree=null;
        Object string_literal10_tree=null;
        RewriteRuleTokenStream stream_TEXT=new RewriteRuleTokenStream(adaptor,"token TEXT");
        RewriteRuleTokenStream stream_8=new RewriteRuleTokenStream(adaptor,"token 8");
        RewriteRuleTokenStream stream_11=new RewriteRuleTokenStream(adaptor,"token 11");

        try {
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:24:2: ( '<body>' TEXT '</body>' -> ^( 'body' TEXT ) )
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:24:4: '<body>' TEXT '</body>'
            {
            string_literal8=(Token)match(input,11,FOLLOW_11_in_html_body104);  
            stream_11.add(string_literal8);


            TEXT9=(Token)match(input,TEXT,FOLLOW_TEXT_in_html_body106);  
            stream_TEXT.add(TEXT9);


            string_literal10=(Token)match(input,8,FOLLOW_8_in_html_body108);  
            stream_8.add(string_literal10);


            // AST REWRITE
            // elements: TEXT, BODY
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            // wildcard labels: 
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.tree:null);

            root_0 = (Object)adaptor.nil();
            // 24:28: -> ^( 'body' TEXT )
            {
                // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:24:31: ^( 'body' TEXT )
                {
                Object root_1 = (Object)adaptor.nil();
                root_1 = (Object)adaptor.becomeRoot(
                (Object)adaptor.create(BODY, "BODY")
                , root_1);

                adaptor.addChild(root_1, 
                stream_TEXT.nextNode()
                );

                adaptor.addChild(root_0, root_1);
                }

            }


            retval.tree = root_0;

            }

            retval.stop = input.LT(-1);


            retval.tree = (Object)adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }

        finally {
        	// do for sure before leaving
        }
        return retval;
    }
    // $ANTLR end "html_body"

    // Delegated rules


 

    public static final BitSet FOLLOW_12_in_html_doc57 = new BitSet(new long[]{0x0000000000002000L});
    public static final BitSet FOLLOW_html_header_in_html_doc59 = new BitSet(new long[]{0x0000000000000800L});
    public static final BitSet FOLLOW_html_body_in_html_doc61 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_9_in_html_doc63 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_13_in_html_header82 = new BitSet(new long[]{0x0000000000000040L});
    public static final BitSet FOLLOW_TEXT_in_html_header84 = new BitSet(new long[]{0x0000000000000400L});
    public static final BitSet FOLLOW_10_in_html_header86 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_11_in_html_body104 = new BitSet(new long[]{0x0000000000000040L});
    public static final BitSet FOLLOW_TEXT_in_html_body106 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_8_in_html_body108 = new BitSet(new long[]{0x0000000000000002L});

}