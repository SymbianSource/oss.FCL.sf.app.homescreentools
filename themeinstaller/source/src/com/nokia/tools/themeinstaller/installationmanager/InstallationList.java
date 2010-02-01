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
* Description:  Installation list for monitoring language variants under install.
 *
*/


package com.nokia.tools.themeinstaller.installationmanager;

import java.util.Vector;

/**
 * Installation list for monitoring language variants under install.
 */
public class InstallationList
    {

    // CONSTANTS
    private static final int NOT_FOUND = -1;
    private static final String EXT_PREFIX = ".o";

    // Languages under install
    private Vector iLanguages;

    /**
     * Constructor.
     */
    public InstallationList()
        {
        iLanguages = new Vector();
        }

    /**
     * Add a language under install.
     * @param aLanguage language id
     */
    public void addInstall( Integer aLanguage )
        {
        iLanguages.add( aLanguage );
        }

    /**
     * Remove a language from list when the installation has completed.
     * @param aODTFileName path and file name of the installed ODT.
     * @return true if a language was removed from the list
     */
    public boolean removeInstall( String aODTFileName )
        {
        // No localized as default
        int languageId = NOT_FOUND;
        int extIndex = NOT_FOUND;
        if( aODTFileName != null )
            {
            extIndex = aODTFileName.lastIndexOf( EXT_PREFIX );
            }
        if( extIndex >= 0 )
            {
            String language = aODTFileName.substring( extIndex + EXT_PREFIX.length() );
            if( language != null &&
               !language.equals( "" ) )
                {
                languageId = Integer.valueOf( language ).intValue();
                }
            }

        return removeInstall( languageId );
        }

    /**
     * Remove a language from list when the installation has completed.
     * @param aLanguage language id
     * @return true if a language was removed from the list
     */
    public boolean removeInstall( int aLanguage )
        {
        boolean result = false;
        int index = findLanguage( aLanguage );
        if( index >= 0 )
            {
            iLanguages.remove( index );
            result = true;
            }

        return result;
        }

    /**
     * Check if there are ongoing installations in the list.
     * @return true if there are installtions in the list
     */
    public boolean installsExist()
        {
        if( iLanguages.size() > 0 )
            {
            return true;
            }
        return false;
        }

    /**
     * Find a language from the list.
     * @param aLanguage language id
     * @return index of the language in the list
     */
    private int findLanguage( int aLanguage )
        {
        int count = iLanguages.size();
        for( int i = 0; i < count; i++ )
            {
            Integer integer = ( Integer ) iLanguages.elementAt( i );
            if( integer.intValue() == aLanguage )
                {
                return i;
                }
            }

        return NOT_FOUND;
        }

    }
