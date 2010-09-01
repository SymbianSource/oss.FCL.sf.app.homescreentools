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
* Description:  This class gets notified during the CSS file parsing
 *
*/


package com.nokia.tools.themeinstaller.cssparser;

import java.awt.Color;
import java.io.File;
import java.io.FileReader;
import java.io.Reader;
import java.util.HashMap;
import java.util.Vector;

import org.w3c.css.sac.CSSException;
import org.w3c.css.sac.DocumentHandler;
import org.w3c.css.sac.InputSource;
import org.w3c.css.sac.LexicalUnit;
import org.w3c.css.sac.Parser;
import org.w3c.css.sac.SACMediaList;
import org.w3c.css.sac.SelectorList;
import org.w3c.css.sac.helpers.ParserFactory;
import org.w3c.dom.Document;

import com.nokia.tools.themeinstaller.logger.LogWriter;

/**
 * The Class CSSHandler. Informs application of basic parsing events. This
 * should be registered with CSS Parser with setDocumentHandler method.
 *
 * Handler gets notified during the CSS parsing:
 * 1. startSelector(), when new selector is noticed
 * 2. property(), when new property is noticed
 * 3. lexicalValue() is used to calculate the values of the parsed property
 *
 * If you are using CSS import with paths relative to main CSS, you need to
 * set the path of main CSS using setImportDirectory( String aImportDirectory )
 */

public class CSSHandler implements DocumentHandler
    {

    /** The style map for style property. */
    private HashMap iStyleMap;

    /** List of parsed rules. */
    private Vector iRuleList;

    /** The DOM document. */
    private Document iDocument;

    /** Color resolver for resolving colors in string form */
    private ColorResolver iColorResolver;

    /** The main CSS directory for finding imported CSS File's relative path. */
    private String iImportDirectory;

    /** The Constant FUNCTION_HSL. */
    public static final String FUNCTION_HSL = "hsl";

    /** The Constant COMMA. */
    public static final String COMMA = ",";

    /** The Constant CHAR_APOSTROPHE. */
    private static final char CHAR_APOSTROPHE = '"';

    /** The Constant CHAR_SPACE. */
    private static final char CHAR_SPACE = ' ';

    /** The Constant CHAR_COLON. */
    private static final char CHAR_COLON = ':';

    /** The Constant SEPARATOR. */
    public static final String SEPARATOR = "|";

    /** The Constant FORWARD_SLASH. */
    public static final String FORWARD_SLASH = "/";

    /** The Constant BACKWARD_SLASH. */
    public static final String BACKWARD_SLASH = "\\";

    /** The CSS to DOM Processor for applying changes to DOM. */
    private CSSDOMProcessor iCSSDOMProcessor;

    /**
     * Instantiates a new CSS handler.
     */
    public CSSHandler()
        {
        super();
        iCSSDOMProcessor = new CSSDOMProcessor();
        iStyleMap = new HashMap();
        iRuleList = new Vector();
        iColorResolver = new ColorResolver();
        }

    /**
     * Instantiates a new CSS handler. This one is used for handling imported
     * CSS files
     *
     * @param aHandler The handler to retrieve previous rule list and DOM document
     *            from
     */
    private CSSHandler( CSSHandler aHandler )
        {
        super();
        iCSSDOMProcessor = new CSSDOMProcessor();
        iStyleMap = new HashMap();

        iRuleList = aHandler.iRuleList;
        iDocument = aHandler.iDocument;
        iColorResolver = new ColorResolver();
        }

    /**
     * Sets the document.
     *
     * @param aDocument The new document
     */
    public void setDocument( Document aDocument )
        {
        iDocument = aDocument;
        }

    /**
     * Gets the document.
     *
     * @return the document
     */
    public Document getDocument()
        {
        return iDocument;
        }

    /**
     * Sets the directory of main CSS.
     *
     * @param aImportDirectory The directory of main CSS
     */
    public void setImportDirectory( String aImportDirectory )
        {
        iImportDirectory = aImportDirectory;
        }

    /*
     * (non-Javadoc)
     *
     * @see org.w3c.css.sac.DocumentHandler#startDocument(org.w3c.css.sac.InputSource)
     */
    public void startDocument( InputSource arg0 ) throws CSSException
        {
        iRuleList = new Vector();
        }

    /*
     * (non-Javadoc)
     *
     * @see org.w3c.css.sac.DocumentHandler#startSelector(org.w3c.css.sac.SelectorList)
     */
    public void startSelector( SelectorList aSelectorList ) throws CSSException
        {
        iStyleMap = new HashMap();
        }

    /*
     * (non-Javadoc)
     *
     * @see org.w3c.css.sac.DocumentHandler#endSelector(org.w3c.css.sac.SelectorList)
     */
    public void endSelector( SelectorList aSelectors ) throws CSSException
        {
        if ( iStyleMap.size() != 0 )
            {
            for ( int i = 0; i < aSelectors.getLength(); i++ )
                {
//            	System.out.println("CSSHandler Selectors --> "+aSelectors.item(i));
                CSSRule rule = new CSSRule( aSelectors.item( i ), iStyleMap );
                iRuleList.add( rule );
                }
            }
        }

    /*
     * (non-Javadoc)
     *
     * @see org.w3c.css.sac.DocumentHandler#property(java.lang.String,
     *      org.w3c.css.sac.LexicalUnit, boolean)
     */
    public void property( String aName, LexicalUnit aLexicalUnit,
            boolean aImportant ) throws CSSException
        {
        Vector propertyValues = new Vector();
        lexicalValue( aLexicalUnit, propertyValues );
        iStyleMap.put( aName, new CSSStyleProperty( propertyValues, aImportant ) );
        }

    /*
     * (non-Javadoc)
     *
     * @see org.w3c.css.sac.DocumentHandler#endDocument(org.w3c.css.sac.InputSource)
     */
    public void endDocument( InputSource aInputSource ) throws CSSException
        {
        if ( iDocument == null )
            {
            throw new IllegalStateException( "CSSHandler has null DOM Document" );
            }
        
        iCSSDOMProcessor.applyRulesToDom( iDocument, iRuleList );
        }


    /**
     * Finds out the property values and adds them into a Vector
     * aPropertyValues. Property types that are taken into account are
     * from Symbian side: ...\Xuikon\Dom\src\xndompropertyvalue.cpp
     *
     * @param aLexicalUnit Value
     * @param aPropertyValues Vector for Property values
     */
    public void lexicalValue( LexicalUnit aLexicalUnit,
            Vector aPropertyValues )
        {
        while ( aLexicalUnit != null )
            {
            switch ( aLexicalUnit.getLexicalUnitType() )
                {
                case LexicalUnit.SAC_OPERATOR_COMMA:
                    break;
                // Allowed cases for integer value
                case LexicalUnit.SAC_INTEGER:
                    aPropertyValues
                            .add( new CSSPropertyValue(
                                    LexicalUnit.SAC_INTEGER, Integer
                                            .toString( aLexicalUnit
                                                    .getIntegerValue() ) ) );
                    break;
                // Allowed cases for real value
                // Fallthrough
                case LexicalUnit.SAC_REAL:
                case LexicalUnit.SAC_DIMENSION:
                case LexicalUnit.SAC_EM:
                case LexicalUnit.SAC_EX:
                case LexicalUnit.SAC_INCH:
                case LexicalUnit.SAC_PIXEL:
                case LexicalUnit.SAC_CENTIMETER:
                case LexicalUnit.SAC_MILLIMETER:
                case LexicalUnit.SAC_POINT:
                case LexicalUnit.SAC_PICA:
                case LexicalUnit.SAC_PERCENTAGE:
                case LexicalUnit.SAC_DEGREE:
                case LexicalUnit.SAC_GRADIAN:
                case LexicalUnit.SAC_RADIAN:
                case LexicalUnit.SAC_MILLISECOND:
                case LexicalUnit.SAC_SECOND:
                case LexicalUnit.SAC_HERTZ:
                case LexicalUnit.SAC_KILOHERTZ:
                    aPropertyValues.add( new CSSPropertyValue( aLexicalUnit
                            .getLexicalUnitType(), Float.toString( aLexicalUnit
                            .getFloatValue() ) ) );
                    break;
                // RGB Values
                case LexicalUnit.SAC_RGBCOLOR:
                    //Using StringBuffer to store values of RGB property
                    //in order to handle values (R,G and B) as one value
                    StringBuffer sb = new StringBuffer();
                    colorValue( aLexicalUnit.getParameters(), sb );
                    aPropertyValues.add( new CSSPropertyValue( aLexicalUnit
                            .getLexicalUnitType(), sb.toString() ) );
                    break;
                // Allowed cases for string values
                // Fallthrough
                case LexicalUnit.SAC_URI:
                case LexicalUnit.SAC_IDENT:
                case LexicalUnit.SAC_STRING_VALUE:
                case LexicalUnit.SAC_ATTR:
                    // Color value as string
                    if ( iColorResolver.get( aLexicalUnit.getStringValue() ) != null )
                        {
                        Color color = ( Color ) iColorResolver.get( aLexicalUnit
                                .getStringValue() );
                        aPropertyValues.add( new CSSPropertyValue(
                                LexicalUnit.SAC_RGBCOLOR,
                                LexicalUnit.SAC_INTEGER + SEPARATOR
                                        + color.getRed() + COMMA
                                        + LexicalUnit.SAC_INTEGER + SEPARATOR
                                        + color.getGreen() + COMMA
                                        + LexicalUnit.SAC_INTEGER + SEPARATOR
                                        + color.getBlue() ) );
                        }
                    // Space
                    else if ( aLexicalUnit.getStringValue()
                            .indexOf( CHAR_SPACE ) != -1 )
                        {
                        aPropertyValues.add( new CSSPropertyValue( aLexicalUnit
                                .getLexicalUnitType(), CHAR_APOSTROPHE
                                + aLexicalUnit.getStringValue()
                                + CHAR_APOSTROPHE ) );
                        }
                    // Text
                    else
                        {
                        aPropertyValues.add( new CSSPropertyValue( aLexicalUnit
                                .getLexicalUnitType(), aLexicalUnit
                                .getStringValue() ) );
                        }
                    break;
                // In case value is set as "inherit" already in CSS -file
                // This sets it to DOM as Ident value that is "inherit"
                case LexicalUnit.SAC_INHERIT:
                    aPropertyValues.add( new CSSPropertyValue(
                            LexicalUnit.SAC_IDENT,
                            CSSDOMProcessor.STRING_INHERIT ) );
                    break;
                case LexicalUnit.SAC_FUNCTION:
                    String functionName = aLexicalUnit.getFunctionName();
                    if ( functionName.equals( FUNCTION_HSL ) )
                        {
                        Color color = colorFromHsl( aLexicalUnit
                                .getParameters() );
                        aPropertyValues.add( new CSSPropertyValue(
                                LexicalUnit.SAC_RGBCOLOR,
                                LexicalUnit.SAC_INTEGER + SEPARATOR
                                        + color.getRed() + COMMA
                                        + LexicalUnit.SAC_INTEGER + SEPARATOR
                                        + color.getGreen() + COMMA
                                        + LexicalUnit.SAC_INTEGER + SEPARATOR
                                        + color.getBlue() ) );

                        }
                    else
                        {
                        throw new IllegalStateException(
                                "Unknown CSS Function : " + functionName );
                        }
                    break;
                default:
                    break;
                }
            aLexicalUnit = aLexicalUnit.getNextLexicalUnit();
            }
        }

    /**
     * Parses HSL Function using ColorResolver.
     *
     * @param aLexicalUnit Parameters containing color values
     *
     * @return the color
     */
    private Color colorFromHsl( LexicalUnit aLexicalUnit )
        {
        float h = 0;
        float s = 0;
        float l = 0;
        try
            {
            h = ( float ) aLexicalUnit.getIntegerValue();
            aLexicalUnit = aLexicalUnit.getNextLexicalUnit()
                    .getNextLexicalUnit();
            s = aLexicalUnit.getFloatValue();
            aLexicalUnit = aLexicalUnit.getNextLexicalUnit()
                    .getNextLexicalUnit();
            l = aLexicalUnit.getFloatValue();
            }
        catch ( RuntimeException e )
            {
            throw new IllegalStateException( "Illegal HSL Color values" );
            }
        if ( aLexicalUnit.getNextLexicalUnit() != null )
            {
            throw new IllegalStateException( "Too many parameters in HSL color" );
            }
        return iColorResolver.hslToRgb( h, s, l );
        }

    /**
     * Finds out the property values for RGB color and adds them into a
     * StringBuffer aProperty.
     *
     * @param aLexicalUnit Parameters containing color values
     * @param aProperty StringBuffer for storing property information
     */
    public void colorValue( LexicalUnit aLexicalUnit, StringBuffer aProperty )
        {
        while ( aLexicalUnit != null )
            {
            switch ( aLexicalUnit.getLexicalUnitType() )
                {
                // Operator ","
                case LexicalUnit.SAC_OPERATOR_COMMA:
                    aProperty.append( COMMA );
                    break;
                case LexicalUnit.SAC_INTEGER:
                    aProperty.append( aLexicalUnit.getLexicalUnitType() );
                    aProperty.append( SEPARATOR );
                    aProperty.append( aLexicalUnit.getIntegerValue() );
                    break;
                case LexicalUnit.SAC_PERCENTAGE:
                    aProperty.append( LexicalUnit.SAC_INTEGER );
                    aProperty.append( SEPARATOR );
                    aProperty.append( iColorResolver
                            .getColorValueFromPercentage( aLexicalUnit
                                    .getFloatValue() ) );
                    break;
                default:
                    break;
                }
            aLexicalUnit = aLexicalUnit.getNextLexicalUnit();
            }
        }

    /*
     * (non-Javadoc)
     *
     * @see org.w3c.css.sac.DocumentHandler#startFontFace ()
     */
    public void startFontFace() throws CSSException
        {
        }

    /*
     * (non-Javadoc)
     *
     * @see org.w3c.css.sac.DocumentHandler#startPage(java.lang.String,
     *      java.lang.String)
     */
    public void startPage( String arg0, String arg1 ) throws CSSException
        {
        }

    /*
     * (non-Javadoc)
     *
     * @see org.w3c.css.sac.DocumentHandler#endFontFace ()
     */
    public void endFontFace() throws CSSException
        {
        }

    /*
     * (non-Javadoc)
     *
     * @see org.w3c.css.sac.DocumentHandler#endPage(java.lang.String,
     *      java.lang.String)
     */
    public void endPage( String arg0, String arg1 ) throws CSSException
        {
        }

    /*
     * (non-Javadoc)
     *
     * @see org.w3c.css.sac.DocumentHandler#comment (java.lang.String)
     */
    public void comment( String arg0 ) throws CSSException
        {
        }

    /*
     * (non-Javadoc)
     *
     * @see org.w3c.css.sac.DocumentHandler#endMedia (org.w3c.css.sac.SACMediaList)
     */
    public void endMedia( SACMediaList arg0 ) throws CSSException
        {
        }

    /*
     * (non-Javadoc)
     *
     * @see org.w3c.css.sac.DocumentHandler#ignorableAtRule (java.lang.String)
     */
    public void ignorableAtRule( String arg0 ) throws CSSException
        {
        }

    /*
     * (non-Javadoc)
     *
     * @see org.w3c.css.sac.DocumentHandler#importStyle (java.lang.String,
     *      org.w3c.css.sac.SACMediaList, java.lang.String)
     */
    public void importStyle( String aCSSFileName, SACMediaList aMedia,
            String aNameSpaceUri ) throws CSSException
        {
        try
            {
            CSSHandler handler = new CSSHandler( this );
            ParserFactory factory = new ParserFactory();

            Parser parser = factory.makeParser();
            parser.setDocumentHandler( handler );
            Reader r = null;

            File cssImport = new File( aCSSFileName );
            if ( isAbsolutePath( aCSSFileName ) && cssImport.exists() )
                {
                // The imported CSS file is given with absolute path
                r = new FileReader( aCSSFileName );
                LogWriter.getInstance().logInfo(
                        "Imported CSS : " + cssImport.getAbsolutePath() );
                }
            else if ( !isAbsolutePath( aCSSFileName )
                    && iImportDirectory != null )
                {
                // If the given imported CSS File is not found,
                // try to locate it using path relative to main CSS
                File relativeCSS = new File( iImportDirectory + File.separator
                        + aCSSFileName );
                r = new FileReader( relativeCSS );
                LogWriter.getInstance().logInfo(
                        "Imported CSS : " + relativeCSS.getAbsolutePath() );
                }
            else
                {
                throw new IllegalStateException(
                        "Can't resolve imported CSS File: " + aCSSFileName );
                }

            InputSource is = new InputSource( r );
            parser.parseStyleSheet( is );
            }
        catch ( Exception e )
            {
            throw new CSSException( e.getMessage() );
            }
        }

    /**
     * Checks if path is absolute path.
     * Path is absolute if it starts with '/', '\'
     * or is of form [drive]:[path]
     * @param aFilePath the a file path
     *
     * @return true, if is absolute path
     */
    private boolean isAbsolutePath( String aFilePath )
        {
        if ( aFilePath.startsWith( FORWARD_SLASH ) )
            {
            return true;
            }
        if ( aFilePath.startsWith( BACKWARD_SLASH ) )
            {
            return true;
            }
        if ( aFilePath.length() > 1 && aFilePath.charAt( 1 ) == CHAR_COLON )
            {
            return true;
            }
        return false;
        }

    /*
     * (non-Javadoc)
     *
     * @see org.w3c.css.sac.DocumentHandler#namespaceDeclaration(java.lang.String,
     *      java.lang.String)
     */
    public void namespaceDeclaration( String arg0, String arg1 )
            throws CSSException
        {
        }

    /*
     * (non-Javadoc)
     *
     * @see org.w3c.css.sac.DocumentHandler#startMedia(org.w3c.css.sac.SACMediaList)
     */
    public void startMedia( SACMediaList arg0 ) throws CSSException
        {
        }

    }
