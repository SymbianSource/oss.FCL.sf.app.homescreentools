/*
* Copyright (c) 2008 Nokia Corporation and/or its subsidiary(-ies). 
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
* Description:  Event for installation progress information.
 *
*/

package com.nokia.tools.themeinstaller.installationmanager;

/**
 * Installation progress event for delivering information about parsed
 * resource files and installed ODT files.
 */
public class ProgressEvent
    {

    // Installation iState
    private int iState;

    // Theme name
    private String iName;

    // Language id
    private int iLanguage;

    // Installed file
    private String iFileName;

    // Error code
    private int iError;

    // Message
    private String iMessage;

    /**
     * Constructor.
     */
    public ProgressEvent()
        {
        }

    /**
     * Get installation state.
     * @return the state
     */
    public int getState()
        {
        return iState;
        }

    /**
     * Get theme name.
     * @return the name
     */
    public String getName()
        {
        return iName;
        }

    /**
     * Get the language id under install.
     * @return the language
     */
    public int getLanguage()
        {
        return iLanguage;
        }

    /**
     * Get name of the installed ODT file, if any
     * @return the fileName
     */
    public String getFileName()
        {
        return iFileName;
        }

    /**
     * Get the error code
     * @return the error code
     */
    public int getError()
        {
        return iError;
        }

    /**
     * Get the error message
     * @return the message
     */
    public String getMessage()
        {
        return iMessage;
        }

    /**
     * Set theme name
     * @param aName the name to set
     */
    public void setName( String aName )
        {
        iName = aName;
        }

    /**
     * Set language variant
     * @param aLanguage the language to set
     */
    public void setLanguage( int aLanguage )
        {
        iLanguage = aLanguage;
        }

    /**
     * Set state
     * @param iError the error to set
     */
    public void setState( int aState )
        {
        iState = aState;
        }

    /**
     * Set name of the installed ODT file
     * @param aFileName the fileName to set
     */
    public void setFileName( String aFileName )
        {
        iFileName = aFileName;
        }

    /**
     * Set error code and message
     * @param aError the error to set
     * @param aMessage the message to set
     */
    public void setError( int aError, String aMessage )
        {
        iError = aError;
        iMessage = aMessage;
        }

    /**
     * Set the error message
     * @param aMessage the message to set
     */
    public void setMessage( String aMessage )
        {
        iMessage = aMessage;
        }


    }
