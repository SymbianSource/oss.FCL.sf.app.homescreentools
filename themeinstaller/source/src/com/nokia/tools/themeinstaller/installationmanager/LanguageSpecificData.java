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
* Description:  Contains language specific data of each language.
 *
*/


package com.nokia.tools.themeinstaller.installationmanager;

import java.util.Vector;

/**
 * Contains all the language specific data.
 */
public class LanguageSpecificData
    {

    // Language id according to TLanguage enumeration in e32const.h
    private Integer iLanguageId;

    // DTD file name of the language
    private String iFileDTD;

    // CSS file name of the language
    private String iFileCSS;

    // Localized theme full name
    private String iThemeFullName;

    // Language specific resource files
    private Vector iResources;

    /**
     * Constructor.
     * @param aLanguageId Id number of the language
     * @param aFileDTD DTD file name
     * @param aFileCSS CSS file name
     * @param aThemeFullName Localized theme full name
     * @param aResources List of language specific resource files
     */
    public LanguageSpecificData( Integer aLanguageId,
                                 String aFileDTD,
                                 String aFileCSS,
                                 String aThemeFullName,
                                 Vector aResources )
        {
        iLanguageId = aLanguageId;
        iFileDTD = aFileDTD;
        iFileCSS  = aFileCSS;
        iThemeFullName = aThemeFullName;
        iResources = aResources;
        if( iResources == null )
            {
            iResources = new Vector();
            }
        }

    /**
     * Get language id according to TLanguage enumeration in e32const.h.
     * @return Language id
     */
    public Integer getLanguageId()
        {
        return iLanguageId;
        }

    /**
     * Get DTD file name of the language.
     * @return File name of the DTD file
     */
    public String getDTDFile()
        {
        return iFileDTD;
        }

    /**
     * Get CSS file name of the language.
     * @return File name of the CSS file
     */
    public String getCSSFile()
        {
        return iFileCSS;
        }

    /**
     * Get localized theme full name.
     * @return Localized theme full name
     */
    public String getThemeFullName()
        {
        return iThemeFullName;
        }

    /**
     * Get language specific resource files
     * @return the resource file list
     */
    public Vector getResources()
        {
        return iResources;
        }

    }
