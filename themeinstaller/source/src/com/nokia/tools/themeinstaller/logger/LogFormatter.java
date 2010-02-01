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
* Description:  String formatter for log files
 *
*/


package com.nokia.tools.themeinstaller.logger;

import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.logging.Formatter;
import java.util.logging.Handler;
import java.util.logging.LogRecord;

/**
 * Formats logging string to human readable form.
 */
public class LogFormatter extends Formatter
    {
    // Format for date and time.
    private final static String DATE_FORMAT = "dd/MM/yyyy HH:mm:ss";

    /* (non-Javadoc)
     * @see java.util.logging.Formatter#format(java.util.logging.LogRecord)
     */
    public String format( LogRecord aRec )
        {
        return ( dateToString( DATE_FORMAT, aRec.getMillis() ) + " " + aRec.getLevel() + " "
                + formatMessage( aRec ) + "\n" );
        }

    /* (non-Javadoc)
     * @see java.util.logging.Formatter#getHead(java.util.logging.Handler)
     */
    public String getHead( Handler aHandler )
        {
        return "";
        }

    /* (non-Javadoc)
     * @see java.util.logging.Formatter#getTail(java.util.logging.Handler)
     */
    public String getTail( Handler aHandler )
        {
        return "";
        }

    /**
     * Formats date and time to string based on expression aFormat.
     *
     * @param aFormat expression for date and time
     *
     * @return Date and time in formatted string
     */
    public static String dateToString( String aFormat, long aDateMillis )
        {
        SimpleDateFormat sdf = new SimpleDateFormat( aFormat );
        String dateString = sdf.format( new Date( aDateMillis ) ).toString();
        return dateString;
        }

    }
