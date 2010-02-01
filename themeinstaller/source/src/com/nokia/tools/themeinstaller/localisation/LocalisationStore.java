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
* Description:  Parses the localisation settings file and creates Localisation
 *                instances for each theme under install.
 *
*/


package com.nokia.tools.themeinstaller.localisation;

import java.io.File;
import java.util.Enumeration;
import java.util.Vector;

import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import com.nokia.tools.themeinstaller.installationmanager.Lock;
import com.nokia.tools.themeinstaller.odtconverter.IParseOperationListener;
import com.nokia.tools.themeinstaller.xmlparser.XMLParser;

/**
 * Parses the localisation settings file and creates Localisation
 * instances for each theme under install.
 */
public class LocalisationStore
    {

    // CONSTANTS
    // Localisation settings element names
    private static final String THEME_ELEMENT = "theme";

    // Theme element attributes
    private static final String APP_UID_ATTR = "appuid";
    private static final String PROVIDER_UID_ATTR = "provideruid";
    private static final String THEME_UID_ATTR = "themeuid";

    // DTD elements
    private static final String MAIN_DTD_ELEMENT = "maindtd";
    private static final String SEARCH_TREE_ELEMENT = "searchtree";
    private static final String DIR_ELEMENT = "dir";
    private static final String DTD_INCLUDE_ELEMENT = "dtdinclude";
    private static final String ENTITY_ELEMENT = "entity";

    // DTD include element attributes
    private static final String FILE_ATTR = "file";
    private static final String ALL_ATTR = "all";
    private static final String TRUE = "true";

    // Radix for uid number conversion
    private static final int RADIX = 16;

    // Localisation store
    private Vector iLocalisations;

    // Lock for waiting the parse operation completion
    private Lock iLock;

    // Parsed localisation setting files
    private Vector iParsedFileNames;

    // Singleton instance
    private static LocalisationStore sInstance = null;

    /**
     * Constructor.
     * @param aFileName Localisation settings file
     */
    private LocalisationStore( File aFile )
        {
        iLock = new Lock();
        iLocalisations = new Vector();
        iParsedFileNames = new Vector();
        }

    /**
     * Get a LocalisationStore instance (singleton).
     * @param aFileName Localisation settings file name
     * @return LocalisationStore instance
     */
    public static LocalisationStore getInstance( File aFile )
        {
        if( sInstance == null )
            {
            sInstance = new LocalisationStore( aFile );
            }
        if( !sInstance.alreadyParsed( aFile ) )
            {
            Document d = sInstance.parseSettings( aFile );
            sInstance.createLocalisations( d );
            }

        return sInstance;
        }

    /**
     * Get Localisation instance for a theme. If the localisation
     * can not be found, null is returned.
     * @param aApplicationUid Theme application uid
     * @param aProviderUid Theme provider uid
     * @param aThemeUid Theme uid
     * @return Localisation instance containing the localisation information
     * for the theme
     * @throws IllegalArgumentException if the localisation can not be found
     */
    public Localisation getLocalisation( long aApplicationUid,
            long aProviderUid,
            long aThemeUid )
        {
        Localisation l = findLocalisation(
                aApplicationUid, aProviderUid, aThemeUid );
        if( l == null )
            {
            throw new IllegalArgumentException(
                    "Can't find localisation information with Uid's : ApplicationUid: "
                            + aApplicationUid + ", ProviderUid: "
                            + aProviderUid + ", ThemeUid: " + aThemeUid );
            }

        return l;
        }

    /**
     * Find the Localisation instance from the internal list.
     * @param aApplicationUid Theme application uid
     * @param aProviderUid Theme provider uid
     * @param aThemeUid Theme uid
     * @return Localisation instance containing the localisation information
     * for the theme. If the localisation can not be found, null is returned
     */
    private Localisation findLocalisation( long aApplicationUid,
            long aProviderUid,
            long aThemeUid )
        {
        // Seek through all localisation instances to find the right one
        Enumeration e = iLocalisations.elements();
        Localisation l = null;
        while( e.hasMoreElements() )
            {
            l = ( Localisation )e.nextElement();
            Settings s = l.getSettings();
            if( aApplicationUid == s.getAppUid() &&
                aProviderUid == s.getProviderUid() &&
                aThemeUid == s.getThemeUid() )
                {
                return l;
                }
            }
        return null;
        }

    /**
     * Check if the settings file has already been parsed.
     * @param aSettings Localisation settings
     * @return true if the localisation settings file has already been parsed
     */
    private boolean alreadyParsed( File aSettings )
        {
        Enumeration e = iParsedFileNames.elements();
        while( e.hasMoreElements() )
            {
            String s = ( String )e.nextElement();
            if( s.equals( aSettings.getPath() ) )
                {
                return true;
                }
            }

        return false;
        }

    /**
     * Create localisation instances for the store.
     * @param aDocument DOM Document containing the settings
     */
    private void createLocalisations( Document aDocument )
        {
        // Set application uid
        NodeList nodes = aDocument.getElementsByTagName( THEME_ELEMENT );
        for( int i = 0; i < nodes.getLength(); i++ )
            {
            Settings settings = new Settings();
            Node theme = nodes.item( i );
            NamedNodeMap list = theme.getAttributes();

            // Read application, provider and theme uids from
            // the element attributes
            for ( int j = 0; j < list.getLength(); j++ )
                {
                Node attr = list.item( j );

                if ( attr.getNodeType() == Node.ATTRIBUTE_NODE )
                    {
                    String name = attr.getNodeName();
                    String value = attr.getNodeValue();

                    if( APP_UID_ATTR.equals( name ) )
                        {
                        settings.setAppUid( Long.valueOf(
                                value, RADIX ).longValue() );
                        }
                    else if( PROVIDER_UID_ATTR.equals( name ) )
                        {
                        settings.setProviderUid( Long.valueOf(
                                value, RADIX ).longValue() );
                        }
                    else if( THEME_UID_ATTR.equals( name ) )
                        {
                        settings.setThemeUid( Long.valueOf(
                                value, RADIX ).longValue() );
                        }
                    }
                }

            // Process settings of a theme
            Node element = theme.getFirstChild();
            while( element != null )
                {
                String elementName = element.getNodeName();

                // Process a main dtd element
                if( MAIN_DTD_ELEMENT.equals( elementName ) )
                    {
                    // Search tree
                    Node maindtdChild = element.getFirstChild();
                    while( maindtdChild != null )
                        {
                        if( SEARCH_TREE_ELEMENT.equals(
                                maindtdChild.getNodeName() ) )
                            {
                            settings.addSearchTree( parseSearchTree( maindtdChild ) );
                            }
                        maindtdChild = maindtdChild.getNextSibling();
                        }
                    }
                // Process a dtd include element
                else if( DTD_INCLUDE_ELEMENT.equals( elementName ) )
                    {
                    IncludeSetting incl = new IncludeSetting();

                    // Attributes: file, all
                    NamedNodeMap inclAttr = element.getAttributes();
                    for ( int j = 0; j < inclAttr.getLength(); j++ )
                        {
                        Node attr = inclAttr.item( j );

                        if ( attr.getNodeType() == Node.ATTRIBUTE_NODE )
                            {
                            String name = attr.getNodeName();
                            String value = attr.getNodeValue();

                            if( FILE_ATTR.equals( name ) )
                                {
                                // Set file attribute
                                incl.setFile( value );
                                }
                            else if( ALL_ATTR.equals( name ) )
                                {
                                // Set all attribute
                                incl.setIncludeAll( TRUE.equals( value ) );
                                }
                            }
                        }

                    Node inclNode = element.getFirstChild();
                    while( inclNode != null )
                        {
                        // Search tree
                        if( SEARCH_TREE_ELEMENT.equals( inclNode.getNodeName() ) )
                            {
                            // Add all directories to the search tree
                            incl.addSearchTree( parseSearchTree( inclNode ) );
                            }
                        // Entities
                        else if( ENTITY_ELEMENT.equals( inclNode.getNodeName() ) )
                            {
                            // Add all entity elements
                            incl.addEntity( inclNode.getTextContent() );
                            }

                        inclNode = inclNode.getNextSibling();
                        }

                    settings.addInclude( incl );
                    }
                element = element.getNextSibling();
                }

            // Check if localisation for the theme already exists
            Localisation l = findLocalisation( settings.getAppUid(),
                        settings.getProviderUid(), settings.getThemeUid() );

            if( l == null )
                {
                // Add a new localisation to the store
                iLocalisations.add( new Localisation( settings ) );
                }
            else
                {
                throw new IllegalArgumentException( "Localisation Store: " +
                        "Localisation settings already exists for theme: " +
                        "appuid: " + settings.getAppUid() +
                        ", provideruid: " + settings.getProviderUid() +
                        ", themeuid: " + settings.getThemeUid() );
                }
            }
        }

    /**
     * Read localisation settings file to a DOM Document.
     * @param aSettings Localisation settings file
     * @return DOM Document containing the settings data
     */
    private Document parseSettings( File aSettings )
        {
        // Create a parse operation listener
        IParseOperationListener listener = new IParseOperationListener()
            {
            public void parseOperationCompleted( int aErr, String aReason )
                {
                iLock.unLock();
                if ( aErr != 0 )
                    {
                    throw new IllegalArgumentException(
                            "Localisation settings parsing failed: "
                            + aErr + ", " + aReason );
                    }
                }
            };

        // Parse the settings file
        XMLParser parser = new XMLParser( aSettings.getPath() );
        parser.addListener( listener );

        try
            {
            parser.parse();
            }
        catch ( Exception e )
            {
            throw new IllegalArgumentException(
                    "Localisation settings parsing failed: "
                    + e.getMessage() );
            }

        // Wait for the operation completion
        iLock.lock();

        iParsedFileNames.add( aSettings.getPath() );

        // Return the document that was formed
        return parser.getDOMDocument();
        }

    /**
     * Parse a search tree of child nodes.
     * @param aParent Search tree node of which child nodes define the
     * search directories
     * @return List of directory names as strings
     */
    private Vector parseSearchTree( Node aParent )
        {
        Vector result = new Vector();

        Node dir = aParent.getFirstChild();
        while( dir != null )
            {
            if( DIR_ELEMENT.equals( dir.getNodeName() ) )
                {
                result.add( dir.getTextContent() );
                }
            dir = dir.getNextSibling();
            }

        return result;
        }

    }
