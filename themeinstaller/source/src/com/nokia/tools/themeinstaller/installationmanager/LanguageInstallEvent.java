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
* Description:  An event for informing about language install completion
 *
*/


package com.nokia.tools.themeinstaller.installationmanager;

import com.nokia.tools.themeinstaller.odtconverter.ODTDocument;

/**
 * An event for informing about language install completion.
 */
public class LanguageInstallEvent
    {

    // ODTDocument related to the event
    private ODTDocument iODTDocument;

    // Error code of the finished operation
    private int iErrorCode;

    // Error reason
    private String iReason;

    /**
     * Language install event constructor.
     * @param aODTDocument ODT Document to the event
     * @param aErrorCode Error code of the completed operation
     * @param aReason Error reason
     */
    public LanguageInstallEvent( ODTDocument aODTDocument,
                                 int aErrorCode,
                                 String aReason )
        {
        iODTDocument = aODTDocument;
        iErrorCode = aErrorCode;
        iReason = aReason;
        }

    /**
     * Get the file.
     * @return The file
     */
    public ODTDocument getODTDocument()
        {
        return iODTDocument;
        }

    /**
     * Get the error code.
     * @return The error code
     */
    public int getErrorCode()
        {
        return iErrorCode;
        }

    /**
     * Get the error reason.
     * @return The error code
     */
    public String getReason()
        {
        return iReason;
        }
    }

