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
* Description:  Listener for parsing operations
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

/**
 * Observer interface for parse operation completions.
 */
public interface IParseOperationListener
    {
    // CONSTANTS
    public static final int OPERATION_SUCCESSFUL = 0;
    public static final int SYNTAX_ERROR = -1;
    public static final int SAX_PARSE_ERROR = -2;
    public static final int IO_ERROR = -3;
    public static final int CSS_PARSER_ERROR = -4;
    public static final int EXCEPTION = -5;

    /**
     * Is called when parse operation is completed.
     * @param aErr error code
     * @param aReason completion reason
     */
    public void parseOperationCompleted( int aErr, String aReason );

    }
