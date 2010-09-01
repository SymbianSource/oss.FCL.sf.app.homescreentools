/*
* Copyright (c) 2007 Nokia Corporation and/or its subsidiary(-ies). 
* All rights reserved.
* This component and the accompanying materials are made available
* under the terms of "Eclipse Public License v1.0"
* which accompanies this distribution, and is available
* at the URL "http://www.eclipse.org/legal/epl-v10.html".
*
* Initial Contributors:
* Nokia Corporation - initial contribution.
*
* Contributors:
*
* Description:  This class parses CSS file to DOM document
 *
*/


package com.nokia.tools.themeinstaller.cssparser;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;

import org.w3c.css.sac.InputSource;
import org.w3c.css.sac.Parser;
import org.w3c.css.sac.helpers.ParserFactory;
import org.w3c.dom.Document;

import com.nokia.tools.themeinstaller.logger.LogWriter;
import com.nokia.tools.themeinstaller.odtconverter.ParseOperation;
import com.nokia.tools.themeinstaller.odtconverter.IParseOperationListener;
import com.nokia.tools.themeinstaller.odtconverter.ODTException;

/**
 * CSSParser parses the CSS File and uses CSSHandler to apply the
 * parsed style rules to DOM Document.
 */
public class CSSParser extends ParseOperation implements Runnable
    {

    /** The Constant CSS_PARSER_SYSTEM_VALUE. */
    private static final String CSS_PARSER_SYSTEM_VALUE = "org.w3c.css.sac.parser";

    /** The Constant CSS_PARSER_SYSTEM_KEY. */
    private static final String CSS_PARSER_SYSTEM_KEY = "org.apache.batik.css.parser.Parser";

    /** CSS file name */
    private String iFileName;

    /** The CSS handler. */
    private CSSHandler iCSSHandler;

    /** The CSS parser. */
    private Parser iParser;

    /**
     * Instantiates a new CSS parser.
     *
     * @param aFileName The CSS file name
     */
    public CSSParser( String aFileName )
        {
        iFileName = aFileName;
        ParserFactory factory = new ParserFactory();
        iCSSHandler = new CSSHandler();

        // Store the value-key pair of the used parser in the System
        // environment(JVM)
        System.setProperty( CSS_PARSER_SYSTEM_VALUE, CSS_PARSER_SYSTEM_KEY );
        try
            {
            iParser = factory.makeParser();
            }
        catch ( Exception e )
            {
            throw new IllegalStateException( "Could not load CSS parser" );
            }
        }

    public void setDocument( Document aDocument )
        {
        iDOMDocument = aDocument;
        }

    /**
     * Run the CSS parse operation.
     */
    public void run()
        {
        int error = IParseOperationListener.OPERATION_SUCCESSFUL;
        String reason = "";

        try
            {
            iCSSHandler.setDocument( iDOMDocument );

            File mainCSS = new File( iFileName );
            Reader r = new FileReader( mainCSS );
            // Tell CSS handler the directory for relative import paths,
            // that is, the path of the Main CSS file
            iCSSHandler.setImportDirectory( mainCSS.getParent() );
            InputSource is = new InputSource( r );
            iParser.setDocumentHandler( iCSSHandler );
            LogWriter.getInstance().logInfo(
                    this.getClass().getSimpleName() + ": Parsing CSS "
                            + iFileName );
            iParser.parseStyleSheet( is );
            iDOMDocument = iCSSHandler.getDocument();
            }
        catch ( Exception e )
            {
            reason = e.getMessage();
            error = IParseOperationListener.CSS_PARSER_ERROR;
            }

        super.operationCompleted( error, reason );
        }

    /**
     * Starts CSS parsing in a new thread.
     */
    public void parse() throws IOException, ODTException
        {
        Thread thread = new Thread( this );
        thread.start();
        }

    }
