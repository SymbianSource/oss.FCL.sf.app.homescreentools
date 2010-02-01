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
* Description:  Class representing the theme manifest
 *
*/


package com.nokia.tools.themeinstaller.installationmanager;

import java.io.File;
import java.util.Vector;

/**
 * Class representing the theme manifest.
 */
/**
 * @author vivahanu
 *
 */
public class ThemeManifest implements IThemeManifest
    {

    // Data directory
    private String iDataDir;

    // Resource list
    private Vector iResources;

    // List of language specific data
    private Vector iLanguages;

    // List of manifest files
    private Vector iManifestFiles;

    // Theme properties
    private Long iApplicationUid;
    private Long iProviderUid;
    private Long iThemeUid;
    private String iProviderName;
    private String iThemeFullName;
    private String iThemeShortName;
    private String iThemeVersion;
    private Integer iScreenSizeX;
    private Integer iScreenSizeY;
    private String iXMLFile;
    private String iCSSFile;
    private String iDTDFile;
    private Integer iThemeStatus;
    private String iNameSpace;

    /**
     * Constructor.
     */
    public ThemeManifest()
        {
        iResources = new Vector();
        iLanguages = new Vector();
        iManifestFiles = new Vector();
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getApplicationUid()
     */
    public Long getApplicationUid()
        {
        return iApplicationUid;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getProviderUid()
     */
    public Long getProviderUid()
        {
        return iProviderUid;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getThemeUid()
     */
    public Long getThemeUid()
        {
        return iThemeUid;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getProviderName()
     */
    public String getProviderName()
        {
        return iProviderName;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getThemeFullName()
     */
    public String getThemeFullName()
        {
        return iThemeFullName;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getThemeShortName()
     */
    public String getThemeShortName()
        {
        return iThemeShortName;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getThemeVersion()
     */
    public String getThemeVersion()
        {
        return iThemeVersion;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getScreenSizeX()
     */
    public Integer getScreenSizeX()
        {
        return iScreenSizeX;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getScreenSizeY()
     */
    public Integer getScreenSizeY()
        {
        return iScreenSizeY;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getThemeStatus()
     */
    public Integer getThemeStatus()
        {
        return iThemeStatus;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getXMLFile()
     */
    public String getXMLFile()
        {
        return iXMLFile;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getCSSFile()
     */
    public String getCSSFile()
        {
        return iCSSFile;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getDTDFile()
     */
    public String getDTDFile()
        {
        return iDTDFile;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getResources()
     */
    public Vector getResources()
        {
        return iResources;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getLanguages()
     */
    public Vector getLanguages()
        {
        return iLanguages;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getManifestFiles()
     */
    public Vector getManifestFiles()
        {
        return iManifestFiles;
        }


    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getDataDir()
     */
    public String getDataDir()
        {
        return iDataDir;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#getNameSpace()
     */
    public String getNameSpace()
        {
        return iNameSpace;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#addLanguage(com.nokia.tools.themeinstaller.installationmanager.LanguageSpecificData)
     */
    public void addLanguage( LanguageSpecificData aLanguage )
        {
        iLanguages.add( aLanguage );
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#addManifestFile(java.lang.String)
     */
    public void addManifestFile( String aFileDAT )
        {
        iManifestFiles.add( new File( aFileDAT ) );
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#addResource(com.nokia.tools.themeinstaller.installationmanager.ThemeResource)
     */
    public void addResource( ThemeResource aResource )
        {
        iResources.add( aResource );
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#setApplicationUid(java.lang.Long)
     */
    public void setApplicationUid( Long aApplicationUid )
        {
        iApplicationUid = aApplicationUid;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#setCSSFile(java.lang.String)
     */
    public void setCSSFile( String aFile )
        {
        iCSSFile = aFile;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#setDTDFile(java.lang.String)
     */
    public void setDTDFile( String aFile )
        {
        iDTDFile = aFile;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#setDataDir(java.lang.String)
     */
    public void setDataDir( String aDataDir )
        {
        iDataDir = aDataDir;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#setThemeStatus(java.lang.Integer)
     */
    public void setThemeStatus( Integer aThemeStatus )
        {
        iThemeStatus = aThemeStatus;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#setNameSpace(java.lang.String)
     */
    public void setNameSpace( String aNameSpace )
        {
        iNameSpace = aNameSpace;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#setProviderName(java.lang.String)
     */
    public void setProviderName( String aProviderName )
        {
        iProviderName = aProviderName;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#setProviderUid(java.lang.Long)
     */
    public void setProviderUid( Long aProviderUid )
        {
        iProviderUid = aProviderUid;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#setScreenSizeX(java.lang.Integer)
     */
    public void setScreenSizeX( Integer aScreenSizeX )
        {
        iScreenSizeX = aScreenSizeX;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#setScreenSizeY(java.lang.Integer)
     */
    public void setScreenSizeY( Integer aScreenSizeY )
        {
        iScreenSizeY = aScreenSizeY;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#setThemeFullName(java.lang.String)
     */
    public void setThemeFullName( String aThemeFullName )
        {
        iThemeFullName = aThemeFullName;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#setThemeShortName(java.lang.String)
     */
    public void setThemeShortName( String aThemeShortName )
        {
        iThemeShortName = aThemeShortName;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#setThemeUid(java.lang.Long)
     */
    public void setThemeUid( Long aThemeUid )
        {
        iThemeUid = aThemeUid;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#setThemeVersion(java.lang.String)
     */
    public void setThemeVersion( String aThemeVersion )
        {
        iThemeVersion = aThemeVersion;
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IThemeManifest#setXMLFile(java.lang.String)
     */
    public void setXMLFile( String aFile )
        {
        iXMLFile = aFile;
        }

    }
