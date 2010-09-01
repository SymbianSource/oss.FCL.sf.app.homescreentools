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
* Description:  Writer for logging
 *
*/


package com.nokia.tools.themeinstaller.logger;

import java.io.File;
import java.io.IOException;
import java.util.logging.ConsoleHandler;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Class for writing logs to file or console.
 * This LogWriter is a singleton version of using logging
 * so that there is no need to instantiate Logger in
 * every class that uses logs.
 *
 * NOTE: User of this class has to make sure that closeInstance() is
 * called when logger is no longer used. If this is not called,
 * the used file resources are not closed.
 */
public class LogWriter
    {
    // The logger used in writing.
    private static Logger iLogger = Logger.getLogger( LogWriter.class.getName() );

    // Singleton instance
    private static LogWriter sInstance = null;

    // Filename for log writing
    private static String sLogFileName = null;

    // Log file constants
    private final static String LOG_FILENAME = "ThemeInstaller";
    private final static String UNDERLINE_CHARACTER = "_";
    private final static String LOG_FILENAME_EXTENSION = ".log";

    // Date format for log filename
    private final static String DATE_FORMAT = "yyyyMMdd_HHmmssSS";

    /**
     * Instantiates a new log writer for console.
     *
     * @param aLevel The level
     */
    private LogWriter( Level aLevel )
        {
        iLogger.setLevel( aLevel );
        // If level == OFF, no need to continue the instantiating
        if ( aLevel == Level.OFF )
            {
            return;
            }
        // Disabling parent handlers so that the console handler remains as only
        // handler
        iLogger.setUseParentHandlers( false );
        ConsoleHandler consoleHandler = new ConsoleHandler();
        consoleHandler.setFormatter( new LogFormatter() );
        iLogger.addHandler( consoleHandler );
        }

    /**
     * Instantiates a new log writer for file.
     *
     * @param aDir The directory for log files
     * @param aLevel The level
     */
    private LogWriter( File aDir, Level aLevel )
        {
        try
            {
            iLogger.setLevel( aLevel );
            // If level == OFF, no need to continue the instantiating
            if ( aLevel == Level.OFF )
                {
                return;
                }
            // Disabling parent handlers so that the file handler remains as only
            // handler
            iLogger.setUseParentHandlers( false );

            String filename = validateDir( aDir );

            FileHandler fileHandler = new FileHandler( filename );
            fileHandler.setFormatter( new LogFormatter() );
            iLogger.addHandler( fileHandler );
            }
        catch ( IOException e )
            {
            iLogger.log( Level.SEVERE, "Unable to create logging file.", e );
            }
        }

    /**
     * Gets the level.
     *
     * @return The level
     */
    public Level getLevel()
        {
        return iLogger.getLevel();
        }

    /**
     * Close file.
     */
    private static void closeFile()
        {
        if ( iLogger.getHandlers().length > 0
        // LogWriter has maximum of 1 handler
                && iLogger.getHandlers()[ 0 ] instanceof FileHandler )
            {
            iLogger.getHandlers()[ 0 ].close();
            }
        }

    /**
     * Validate that directory for logging exists.
     *
     * @param aDir The directory
     *
     * @return Log file name
     */
    private String validateDir( File aDir )
        {
        if ( aDir.isFile() )
            {
            throw new IllegalArgumentException( "Invalid log file path. Not a directory: " + aDir );
            }

        // Create directory structure
        if ( !aDir.exists() )
            {
            aDir.mkdirs();
            }

        return aDir + File.separator + LOG_FILENAME + UNDERLINE_CHARACTER
                + LogFormatter.dateToString( DATE_FORMAT, System.currentTimeMillis() )
                + LOG_FILENAME_EXTENSION;
        }

    /**
     * Sets the level for logging.
     *
     * @param level The logging level in scale from 0 to 7
     */
    public void setLevel( int aLevel )
        {
        if ( aLevel < 0 || 7 < aLevel )
            {
            throw new IllegalStateException(
                    "Trying to set invalid logging level" );
            }
        switch ( aLevel )
            {
            case 0:
                iLogger.setLevel( Level.ALL );
                break;
            case 1:
                iLogger.setLevel( Level.FINEST );
                break;
            case 2:
                iLogger.setLevel( Level.FINER );
                break;
            case 3:
                iLogger.setLevel( Level.FINE );
                break;
            case 4:
                iLogger.setLevel( Level.CONFIG );
                break;
            case 5:
                iLogger.setLevel( Level.INFO );
                break;
            case 6:
                iLogger.setLevel( Level.WARNING );
                break;
            case 7:
                iLogger.setLevel( Level.SEVERE );
                break;
            default:
                break;
            }
        }

    /**
     * Check if logger is in console mode.
     *
     * @return true, if Logger is writing on console
     */
    public boolean inConsoleMode()
        {
        if ( iLogger.getHandlers().length > 0
                // LogWriter has maximum of 1 handler
                && iLogger.getHandlers()[ 0 ] instanceof ConsoleHandler )
            {
            return true;
            }
        return false;
        }

    /**
     * Log severe.
     *
     * @param aMessage The message for logging
     */
    public void logSevere( String aMessage )
        {
        iLogger.log( Level.SEVERE, aMessage );
        }

    /**
     * Log warning.
     *
     * @param aMessage The message for logging
     */
    public void logWarning( String aMessage )
        {
        iLogger.log( Level.WARNING, aMessage );
        }

    /**
     * Log info.
     *
     * @param aMessage The message for logging
     */
    public void logInfo( String aMessage )
        {
        iLogger.log( Level.INFO, aMessage );
        }

    /**
     * Log message.
     *
     * @param aMessage The message for logging
     */
    public void logConfig( String aMessage )
        {
        iLogger.log( Level.CONFIG, aMessage );
        }

    /**
     * Log fine.
     *
     * @param aMessage The message for logging
     */
    public void logFine( String aMessage )
        {
        iLogger.log( Level.FINE, aMessage );
        }

    /**
     * Closes singleton resources and removes the singleton instance
     */
    public static synchronized void closeInstance()
        {
        closeFile();
        sInstance = null;
        }

    /**
     * Gets the single instance of LogWriter.
     * Note that initialize method has to be called
     * before this.
     *
     * @return Single instance of LogWriter
     */
    public static synchronized LogWriter getInstance()
        {
        if ( sInstance == null )
            {
            // Initialize method not called yet
            sInstance = new LogWriter( Level.OFF );
            }
        return sInstance;
        }

    /**
     * Initialize new instance of LogWriter.
     * Note that the default logging level is Level.ALL.
     *
     * @param aDir The directory for writing log
     *
     * @throws IOException Signals that an I/O exception has occurred.
     */
    public static void initialize( File aDir ) throws IOException
        {
        // Already initialized if:
        // sInstance is not null AND
        // sLogFileName equals with aLogFile

        if ( sInstance != null &&
           ( sLogFileName != null && aDir != null && sLogFileName.equals( aDir.getPath() ) ||
           ( sLogFileName == null && aDir == null ) ) )
            {
            return;
            }

        // Create a new instance
        // If no log file given, the log is written in console
        if ( aDir == null )
            {
            sInstance = new LogWriter( Level.ALL );
            sLogFileName = null;
            }
        else
            {
            sInstance = new LogWriter( aDir, Level.ALL );
            sLogFileName = aDir.getPath();
            }
        }
    }
