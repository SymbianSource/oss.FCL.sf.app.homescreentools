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
* Description:  Interface for theme manifest
 *
*/


package com.nokia.tools.themeinstaller.installationmanager;

import java.util.Vector;

/**
 * Interface for theme manifest.
 */
public interface IThemeManifest
    {

    /**
     * Get application uid.
     * @return the application uid
     */
    public Long getApplicationUid();

    /**
     * Get provider uid.
     * @return the provider uid
     */
    public Long getProviderUid();

    /**
     * Get theme uid.
     * @return the theme uid
     */
    public Long getThemeUid();

    /**
     * Get provider name.
     * @return the provider name
     */
    public String getProviderName();

    /**
     * Get theme full name (not localized).
     * @return the theme full name
     */
    public String getThemeFullName();

    /**
     * Get theme short name.
     * @return the theme short name
     */
    public String getThemeShortName();

    /**
     * Get theme version.
     * @return the theme version
     */
    public String getThemeVersion();

    /**
     * Get horizontal screen size.
     * @return the screen size x value
     */
    public Integer getScreenSizeX();

    /**
     * Get vertical screen size.
     * @return the screen size y value
     */
    public Integer getScreenSizeY();

    /**
     * Get theme status. Theme status flags are a bit mask created from
     * theme status. See Xuikon for more information.
     * @return the flags
     */
    public Integer getThemeStatus();

    /**
     * Get theme XML file name.
     * @return the XML file name
     */
    public String getXMLFile();

    /**
     * Get theme CSS file name.
     * @return the CSS file name
     */
    public String getCSSFile();

    /**
     * Get theme DTD file name.
     * @return the DTD file name
     */
    public String getDTDFile();

    /**
     * Get all resources.
     * @return the list of resource files
     */
    public Vector getResources();

    /**
     * Get all language specific data.
     * @return the list of languages
     */
    public Vector getLanguages();

    /**
     * Get all manifest files of a multi theme manifest.
     * @return the list of manifest files
     */
    public Vector getManifestFiles();

    /**
     * Get the data directory that contains the theme files.
     * @return the data directory
     */
    public String getDataDir();

    /**
     * Get the name space of the theme.
     * @return the theme name space
     */
    public String getNameSpace();

    /**
     * Set application uid.
     * @param aApplicationUid the application uid
     */
    public void setApplicationUid( Long aApplicationUid );

    /**
     * Set provider uid.
     * @param aProviderUid the provider uid
     */
    public void setProviderUid( Long aProviderUid );

    /**
     * Set theme uid.
     * @param aThemeUid the theme uid
     */
    public void setThemeUid( Long aThemeUid );

    /**
     * Set provider name.
     * @param aProviderName the provider name
     */
    public void setProviderName( String aProviderName );

    /**
     * Set theme full name (not localized).
     * @param aThemeFullName the theme full name
     */
    public void setThemeFullName( String aThemeFullName );

    /**
     * Set theme short name.
     * @param aThemeShortName the theme short name
     */
    public void setThemeShortName( String aThemeShortName );

    /**
     * Set theme version.
     * @param the theme version
     */
    public void setThemeVersion( String aThemeVersion );

    /**
     * Set horizontal screen size.
     * @param aScreenSizeX the screen size x value
     */
    public void setScreenSizeX( Integer aScreenSizeX );

    /**
     * Set vertical screen size.
     * @param aScreenSizeY the screen size y value
     */
    public void setScreenSizeY( Integer aScreenSizeY );

    /**
     * Set theme status. Theme status flags are a bit mask created
     * from theme status. See Xuikon for more information.
     * @param aFlags the flags
     */
    public void setThemeStatus( Integer aThemeStatus );

    /**
     * Set theme XML file name.
     * @param aXMLFile the XML file name
     */
    public void setXMLFile( String aXMLFile );

    /**
     * Set theme CSS file name.
     * @param aCSSFile the CSS file name
     */
    public void setCSSFile( String aCSSFile );

    /**
     * Set theme DTD file name.
     * @param aDTDFile the DTD file name
     */
    public void setDTDFile( String aDTDFile );

    /**
     * Add a resource.
     * @param the resource to add
     */
    public void addResource( ThemeResource aResource );

    /**
     * Add a language.
     * @param the language to add
     */
    public void addLanguage( LanguageSpecificData aLanguage );

    /**
     * Add a manifest file of a multi theme manifest.
     * @param the manifest file name to add
     */
    public void addManifestFile( String aFileDAT );

    /**
     * Set the data directory that contains the theme files.
     * @param aDataDir the data directory
     */
    public void setDataDir( String aDataDir );

    /**
     * Set the name space of the theme.
     * @param aNameSpace the theme name space
     */
    public void setNameSpace( String aNameSpace );
    }
