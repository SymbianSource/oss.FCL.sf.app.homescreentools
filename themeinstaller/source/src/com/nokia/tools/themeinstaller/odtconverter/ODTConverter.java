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
* Description:  Interface class for parse operations
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.io.IOException;

import org.w3c.dom.Document;

import com.nokia.tools.themeinstaller.cssparser.CSSParser;
import com.nokia.tools.themeinstaller.xmlparser.XMLParser;

/**
 * Interface class for parse operations
 */
public class ODTConverter extends ParseOperation
    {

    /** ParserComposite */
    private ParserComposite iParserComposite;

    /** Listener for parse operations */
    IParseOperationListener iListener;

    /**
     * Constructor
     */
    public ODTConverter()
        {
        iParserComposite = new ParserComposite();
        }

    /**
     * Adds the listener.
     *
     * @param aListener listener for parse operations
     */
    public void addListener( IParseOperationListener aListener )
        {
        iParserComposite.addListener( aListener );
        }

    /**
     * Creates XMLParser and adds it to ParserComposite
     * @param aFileName
     */
    public void addXML( String aFileName )
        {
        XMLParser xmlConv = new XMLParser( aFileName );
        iParserComposite.addOperation( xmlConv );
        }

    /**
     * Creates XMLParser and adds it to ParserComposite. By using this method,
     * the XML parser will ignore DTD definition in DOCTYPE. The specified
     * external DTD file is used instead.
     * @param aFileName File name of the XML
     * @param aExtDTD File name of the external DTD
     */
    public void addXML( String aFileName, String aExtDTD )
        {
        XMLParser xmlConv = new XMLParser( aFileName, aExtDTD );
        iParserComposite.addOperation( xmlConv );
        }

    /**
     * Creates CSSParser and adds it to ParserComposite
     * @param aFileName
     */
    public void addCSS( String aFileName )
        {
        CSSParser cssConv = new CSSParser( aFileName );
        iParserComposite.addOperation( cssConv );
        }


    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.odtconverter.ParseOperation#parse()
     */
    public void parse( ) throws IOException, ODTException
        {
        iParserComposite.parse( );
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.odtconverter.ParseOperation#getDOMDocument()
     */
    public Document getDOMDocument()
        {
        return iParserComposite.getDOMDocument();
        }

    }
