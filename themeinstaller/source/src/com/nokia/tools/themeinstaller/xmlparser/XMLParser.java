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
* Description:  Parses XML file to DOM Document
 *
*/


package com.nokia.tools.themeinstaller.xmlparser;

import java.io.IOException;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import com.nokia.tools.themeinstaller.logger.LogWriter;
import com.nokia.tools.themeinstaller.odtconverter.IParseOperationListener;
import com.nokia.tools.themeinstaller.odtconverter.ParseOperation;

/**
 * Parses XML File to DOM Document.
 */
public class XMLParser extends ParseOperation implements Runnable
    {

    // CONSTANTS
    // Document Builder Factory and Parser configuration
    private static final String DBF_KEY =
            "javax.xml.parsers.DocumentBuilderFactory";
    private static final String DBF_VALUE =
            "org.apache.xerces.jaxp.DocumentBuilderFactoryImpl";
    private static final String PARSER_CONFIG_KEY =
            "org.apache.xerces.xni.parser.XMLParserConfiguration";
    private static final String PARSER_CONFIG_VALUE =
            "org.apache.xerces.parsers.XIncludeAwareParserConfiguration";

    /** The Document Builder. */
    private DocumentBuilder iDocumentBuilder;

    /** XML file name */
    private String iFileName;

    /**
     * Static block.
     */
    static
        {
        // Configure the Document Builder Factory
        System.setProperty( DBF_KEY, DBF_VALUE );

        // Configure the XML Parser Configuration
        System.setProperty( PARSER_CONFIG_KEY, PARSER_CONFIG_VALUE );
        }

    /**
     * Instantiates a new XML parser without an external DTD file.
     *
     * @param aFileName the XML file name
     */
    public XMLParser( String aFileName )
        {
        this( aFileName, null );
        }

    /**
     * Instantiates a new XML parser. External DTD file can be used instead of
     * the one defined in the DOCTYPE.
     *
     * @param aFileName the XML file name
     * @param aExtDTD the DTD file name. If an external DTD is not specified,
     * Expand Entity References feature is disabled. This causes the
     * localisation to be left untouched.
     */
    public XMLParser( String aFileName, String aExtDTD )
        {
        super();
        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        dbf.setNamespaceAware( true );

        try
            {
            if( aExtDTD == null )
                {
                // Disable expanding of entity references to leave localisation
                // untouched
                dbf.setExpandEntityReferences( false );

                // Disable the loading of external DTD file because expanding
                // entity references (the localisation) is disabled anyway
                dbf.setFeature(
                        "http://apache.org/xml/features/nonvalidating/load-external-dtd",
                        false );
                }

            // Enable XIncludes in XML parsing
            dbf.setXIncludeAware( true );

            // Disable the adding of XInclude parsing related attributes:
            // xml:base and xml:lang
            dbf.setFeature(
                    "http://apache.org/xml/features/xinclude/fixup-base-uris",
                    false );
            dbf.setFeature(
                    "http://apache.org/xml/features/xinclude/fixup-language",
                    false );

            // Instantiate the Document Builder for parsing
            iDocumentBuilder = dbf.newDocumentBuilder();

            if( aExtDTD != null )
                {
                // Use entity resolver for using an external DTD file
                iDocumentBuilder.setEntityResolver(
                        new DTDEntityResolver( aExtDTD ) );
                }
            }
        catch ( ParserConfigurationException e )
            {
            throw new IllegalStateException( "Could not load XML parser: " + e.toString() );
            }

        iFileName = aFileName;
        }

    /**
     * Run the XML parse operation.
     */
    public void run()
        {
        // Messages for operation listener
        int error = IParseOperationListener.OPERATION_SUCCESSFUL;
        String reason = null;
        try
            {
            // Actual parsing
            LogWriter.getInstance().logInfo(
                    this.getClass().getSimpleName() + ": Parsing " + iFileName );
            iDOMDocument = iDocumentBuilder.parse( iFileName );
            }
        catch ( SAXException e )
            {
            reason = e.getMessage();
            error = IParseOperationListener.SAX_PARSE_ERROR;
            }
        catch ( IOException e )
            {
            reason = e.getMessage();
            error = IParseOperationListener.IO_ERROR;
            }

        super.operationCompleted( error, reason );
        }

    /**
     * Starts XML parsing in a new thread.
     */
    public void parse()
        {
        Thread thread = new Thread( this );
        thread.start();
        }
    }
