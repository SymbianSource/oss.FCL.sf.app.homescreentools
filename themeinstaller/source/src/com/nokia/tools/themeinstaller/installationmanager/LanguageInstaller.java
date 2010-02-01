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
* Description:  Uses ODTConverter for parsing the source files.
 *
*/


package com.nokia.tools.themeinstaller.installationmanager;

import java.io.File;
import java.io.IOException;
import java.util.Observable;
import java.util.Observer;
import java.util.Vector;

import com.nokia.tools.themeinstaller.localisation.Localisation;
import com.nokia.tools.themeinstaller.localisation.LocalisationStore;
import com.nokia.tools.themeinstaller.odtconverter.IParseOperationListener;
import com.nokia.tools.themeinstaller.odtconverter.ODTConverter;
import com.nokia.tools.themeinstaller.odtconverter.ODTDocument;
import com.nokia.tools.themeinstaller.odtconverter.ODTHeader;
import com.nokia.tools.themeinstaller.odtconverter.ODTResource;

/**
 * Language Installer uses the ODTConverter for parsing the source files of
 * a language variant.
 */
public class LanguageInstaller
    extends Observable implements IParseOperationListener
    {

    // ODT Document
    private ODTDocument iODTDocument;

    // ODT Converter
    private ODTConverter iConverter;

    // Theme manifest
    private IThemeManifest iManifest;

    // Language variant
    private LanguageSpecificData iLanguage;

    // Resource files
    private Vector iResources;

    // Resource installer
    private IResourceInstaller iResourceInstaller;

    // Localisation settings file
    private File iLocSettings;

    /**
     * Constructor.
     * @param aListener Listener for the parsing operation conversion
     * @param aManifest Theme manifest
     * @param aLanguage Language variant to to install
     * @param
     */
    public LanguageInstaller( Observer aListener,
                              IThemeManifest aManifest,
                              LanguageSpecificData aLanguage,
                              File aLocSettings,
                              IResourceInstaller aResourceInstaller )
        {
        iODTDocument = new ODTDocument();
        iConverter = new ODTConverter();
        iConverter.addListener( this );
        iManifest = aManifest;
        iLanguage = aLanguage;
        iLocSettings = aLocSettings;
        iResources = new Vector();
        iResourceInstaller = aResourceInstaller;
        addObserver( aListener );
        }

    /**
     * Add ODT Resources. This method can be used i.e. for adding language
     * independent ODT Resources.
     * @param aODTResources a list of resources to add
     */
    public void addResources( Vector aResources )
        {
        iResources.addAll( aResources );
        }

    /**
     * Start the installation process of the language.
     * @throws IOException if parse operation fails
     */
    public void install() throws IOException
        {
        ODTHeader header = createHeader( iManifest, iLanguage );
        iODTDocument.setODTHeader( header );

        // Install and add language specific resources
        Vector langResources = iLanguage.getResources();
        Vector odtLangResources = iResourceInstaller
                .installResources( langResources, header );
        odtLangResources.addAll( iResources );

        // Add ODT file as resource
        ODTResource langODTResource = iResourceInstaller
                .createODTResource( header, iManifest.getNameSpace() );
        odtLangResources.add( langODTResource );
        iODTDocument.setODTResources( odtLangResources );

        String dataDir = iManifest.getDataDir();
        String dtdName = null;
        File dtdFile = null;

        // Determine the DTD file to use
        if( iLanguage.getDTDFile() != null )
            {
            // Language specific DTD
            dtdName = iLanguage.getDTDFile();
            }
        else if( iManifest.getDTDFile() != null )
            {
            // Language independent DTD
            dtdName = iManifest.getDTDFile();
            }

        // Check if enhanced localisation support is enabled
        if( iLocSettings != null && dtdName != null )
            {
            // Use enhanced localisation: Find and compose the DTD file
            LocalisationStore ls = LocalisationStore.getInstance( iLocSettings );
            Localisation l = ls.getLocalisation(
                    iManifest.getApplicationUid().longValue(),
                    iManifest.getProviderUid().longValue(),
                    iManifest.getThemeUid().longValue() );
            dtdFile = l.composeDTD( dtdName, iLanguage.getLanguageId().intValue() );
            }
        else if( dtdName != null )
            {
            // Use the standard localisation
            dtdFile = new File( dataDir + dtdName );
            }

        // Add XML to the converter
        if( dtdFile != null )
            {
            // External DTD file found
            iConverter.addXML( dataDir + iManifest.getXMLFile(),
                               dtdFile.getPath() );
            }
        else
            {
            // Do not use external DTD
            iConverter.addXML( dataDir + iManifest.getXMLFile() );
            }

        // Add CSS to the converter, if available
        if( iLanguage.getCSSFile() != null )
            {
            // Use language specific CSS
            iConverter.addCSS( dataDir + iLanguage.getCSSFile() );
            }
        else if( iManifest.getCSSFile() != null )
            {
            // Use theme specific CSS
            iConverter.addCSS( dataDir + iManifest.getCSSFile() );
            }

        // Start the installation process
        try
            {
            iConverter.parse();
            }
        catch ( Exception e )
            {
            throw new IllegalArgumentException( "Failed to read resource files" );
            }
        }

    /**
     * Creates ODTHeader from manifest data
     * @param aManifest Theme manifest
     * @param aLanguage Language. If language is null, no language
     * specific data is processed.
     * @return new ODT Header
     */
    public static ODTHeader createHeader( IThemeManifest aManifest,
                                    LanguageSpecificData aLanguage )
        {
        ODTHeader header = new ODTHeader();
        if(null!=aManifest.getApplicationUid())
        header.put( ODTHeader.ApplicationUID, aManifest.getApplicationUid() );
        
        if(null!=aManifest.getProviderUid())
        header.put( ODTHeader.ProviderUID, aManifest.getProviderUid() );
        
        if(null!=aManifest.getThemeUid())
        header.put( ODTHeader.ThemeUID, aManifest.getThemeUid() );
        
        if(null!=aManifest.getProviderName())
        header.put( ODTHeader.ProviderName, aManifest.getProviderName() );
        
        if(null!=aManifest.getThemeFullName())
        header.put( ODTHeader.ThemeFullName, aManifest.getThemeFullName() );
        
        if(null!=aManifest.getThemeShortName())
        header.put( ODTHeader.ThemeShortName, aManifest.getThemeShortName() );
        
        if(null!=aManifest.getThemeVersion())
        header.put( ODTHeader.ThemeVersion, aManifest.getThemeVersion() );
        
        if(null!=aManifest.getScreenSizeX())
        header.put( ODTHeader.ScreenSizeX, aManifest.getScreenSizeX() );
        
        if(null!=aManifest.getScreenSizeY())
        header.put( ODTHeader.ScreenSizeY, aManifest.getScreenSizeY() );
        
        if(null!=aManifest.getThemeStatus())
        header.put( ODTHeader.Flags, aManifest.getThemeStatus() );

        // Set language specific data to the header
        if( aLanguage != null )
            {
            // Mandatory fields
            header.put( ODTHeader.Language, aLanguage.getLanguageId() );

            // Optional fields
            String locFullName = aLanguage.getThemeFullName();
            if( locFullName != null )
                {
                header.put( ODTHeader.ThemeFullName, locFullName );
                }
            }

        return header;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.odtconverter.IParseOperationListener#OperationCompleted(int, java.lang.String)
     */
    public void parseOperationCompleted( int aErr, String aReason )
        {
        iODTDocument.setDOMDocument( iConverter.getDOMDocument() );
        super.setChanged();
        super.notifyObservers(
                new LanguageInstallEvent( iODTDocument, aErr, aReason ) );
        }

    }
