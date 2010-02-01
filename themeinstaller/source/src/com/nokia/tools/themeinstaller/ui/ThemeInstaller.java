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
* Description:  Standalone UI
 *
*/


package com.nokia.tools.themeinstaller.ui;

import java.io.File;
import java.io.IOException;
import com.nokia.tools.themeinstaller.installationmanager.IInstallationListener;
import com.nokia.tools.themeinstaller.installationmanager.InstallationManager;
import com.nokia.tools.themeinstaller.installationmanager.InstallationParameters;
import com.nokia.tools.themeinstaller.installationmanager.Lock;
import com.nokia.tools.themeinstaller.installationmanager.ProgressEvent;
import com.nokia.tools.themeinstaller.logger.LogWriter;

public class ThemeInstaller
    {

    // CONSTANTS
    // Error message prefix
    private final static String ERROR_PREFIX = "*** ERROR: ";

    // Usage instructions
    private final static String USAGE =
        "\nUSAGE: ThemeInstaller manifest_file [destination_dir] [-option_1] [-option_n]\n" +
        "\nOptions:" +
        "\n    -loc:<loc_settings_filename.xml>   Enable localisation enhancements" +
        "\n    -prop:<properties_filename.prop>   Use external properties file instead of the default one" +
        "\n    -log:<path>                        Path for log file" +
        "\n    -log                               If no path given, the log is printed to console\n"; 
        //"\n    -fixDTD                            Use if tool should attempt to fix errors in dtd\n";
    

    // Command line options
    private final static String OPTION_PREFIX = "-";
    private final static String LOC_OPTION = "loc:";
    private final static String PROP_OPTION = "prop:";
    private final static String LOG_PATH_OPTION = "log:";
    private final static String LOG_PATH_OPTION_NO_PATH = "log";
    private final static String FIX_INVALID_DTD_PARAMS = "fixDTD";

    // Lock object for waiting the install to complete
    private Lock iLock;

    // Manifest file
    protected String iManifest;

    // Destination directory
    protected String iDestination;

    // Localisation settings file
    protected String iLocSettings;

    // External properties file
    protected String iPropertiesFile;

    // Logging directory
    protected String iLogDir;

    /**
     * Application entry point
     * @param aArgs application arguments
     */
    public static void main( String[] aArgs )
        {
        ThemeInstaller instance = new ThemeInstaller();
        instance.install( aArgs );
        }

    /**
     * Constructor.
     */
    protected ThemeInstaller()
        {
        iLock = new Lock();
        }

    /**
     * Starts the installation process. Parses the arguments before
     * staring the installation.
     * @param aArgs Application arguments
     */
    protected void install( String[] aArgs )
        {
        try
            {
            parseArgs( aArgs );
            }
        catch( IllegalArgumentException iae )
            {
            //System.out.println( ERROR_PREFIX + iae.getMessage() ); 
        	System.out.println("ThemeInstaller version 2.0.0");
        	System.out.println("Copyright (c) 2009 Nokia Corporation and/or its subsidiary(-ies). All rights reserved");
            System.out.println("");
        	System.out.println( USAGE );
            return;
            }
        catch ( IOException e )
            {
            System.out.println( ERROR_PREFIX + e.getMessage() );
            }

        try
            {
            doInstall();
            }
        catch ( Exception e )
            {
            String error = ERROR_PREFIX + "Installation failed: "
                    + e.getMessage();
            if ( !LogWriter.getInstance().inConsoleMode() )
                {
                System.out.println( error );
                }
            LogWriter.getInstance().logSevere( error );
            }
        finally
            {
            LogWriter.closeInstance();
            }
        }

    /**
     * Execute the installation
     * @param aManifest theme manifest file name
     * @param aDestination destination directory
     * @throws Exception if installation fails
     */
    protected void doInstall() throws Exception
        {
        InstallationParameters params = new InstallationParameters(
                new File( iManifest ), new File( iDestination ) );

        LogWriter.getInstance().logInfo( "Starting Installer" );
        LogWriter.getInstance().logInfo( "Manifest file : " + iManifest );
        LogWriter.getInstance().logInfo( "Destination directory : " + iDestination );

        if( iLocSettings != null )
            {
            params.setLocSettings( new File( iLocSettings ) );
            LogWriter.getInstance().logInfo( "Settings file : " + params.getLocSettings().getPath() );
            }
        if( iPropertiesFile != null )
            {
            params.setPropFile( new File ( iPropertiesFile ) );
            LogWriter.getInstance().logInfo( "Properties file : " + params.getPropFile().getPath() );
            }

        IInstallationListener listener = new IInstallationListener()
            {
            public void installationCompleted( ProgressEvent aEvent )
                {
                if( aEvent.getError() == IInstallationListener.NO_ERROR )
                    {
                    if ( !LogWriter.getInstance().inConsoleMode() )
                        {
                        System.out.println( "Installation done." );
                        }
                    LogWriter.getInstance().logInfo( "Installation done" );
                    }
                else
                    {
                    String error = ERROR_PREFIX
                                + "Installation failed, error: "
                                + aEvent.getError() + ", "
                                + aEvent.getMessage();
                    if ( !LogWriter.getInstance().inConsoleMode() )
                            {
                            System.out.println( error );
                            }
                        LogWriter.getInstance().logSevere( error );
                        }

                // release lock
                iLock.unLock();
                }

            public void installationProgress( ProgressEvent aEvent )
                {
                if( aEvent.getState() == IInstallationListener.STATE_PARSED )
                    {
                		String message = "Resource files parsing done,";
                		if( aEvent.getError() != IInstallationListener.NO_ERROR ) {
                			message += " error: " + aEvent.getError() + ",";
                		}
                		message +=  " theme: "
                        + aEvent.getName() + ", language: "
                        + aEvent.getLanguage();
                    
                                
                    if ( !LogWriter.getInstance().inConsoleMode() )
                        {
                        System.out.println( message );
                        }
                    LogWriter.getInstance().logInfo( message );
                    }
                else if ( aEvent.getState() == IInstallationListener.STATE_WRITED )
                    {
                    String message = "Installed ODT: "
                            + aEvent.getFileName();
                    if ( !LogWriter.getInstance().inConsoleMode() )
                        {
                        System.out.println( message );
                        }
                    LogWriter.getInstance().logInfo( message );
                    }
                }
            };

        InstallationManager i = new InstallationManager( params, listener );
        i.startInstallation();

        // wait for finalization
        iLock.lock();
        }

    /**
     * Parse command line arguments.
     * @param aArgs Command line arguments
     * @throws IllegalArgumentException if mandatory command line parameters
     * are not defined
     * @throws IOException Signals that an I/O exception has occurred.
     */
    protected void parseArgs( String[] aArgs ) throws IllegalArgumentException,
            IOException
        {
        // Print usage information if mandatory arguments were not specified
        if( aArgs.length == 0 )
            {
            throw new IllegalArgumentException( "No command line arguments" );
            }

        // Resolve manifest file name and destination directory
        iManifest = aArgs[ 0 ];
        if( aArgs.length > 1 &&
            !aArgs[ 1 ].startsWith( OPTION_PREFIX ) )
            {
            iDestination = aArgs[ 1 ];
            }
        else
            {
            // If no destination directory is specified, use the current dir
            iDestination = System.getProperty( "user.dir" );
            }

        // Parse the options
        for( int i = 1; i < aArgs.length; i++ )
            {
        	//fix DTD
        	String opt = OPTION_PREFIX + FIX_INVALID_DTD_PARAMS;
        	if ( aArgs[ i ].toLowerCase().startsWith( opt.toLowerCase() )) {
        		InstallationManager.setFixDTD(true);
        	}
        	
            // Localisation settings
            opt = OPTION_PREFIX + LOC_OPTION;
            if( aArgs[ i ].startsWith( opt ) )
                {
                iLocSettings = aArgs[ i ].substring( opt.length() );
                if( iLocSettings.length() == 0 )
                    {
                    throw new IllegalArgumentException( "No localisation settings file defined with the option" );
                    }
                }
            // External properties file
            opt = OPTION_PREFIX + PROP_OPTION;
            if( aArgs[ i ].startsWith( opt ) )
                {
                iPropertiesFile = aArgs[ i ].substring( opt.length() );
                if( iPropertiesFile.length() == 0 )
                    {
                    throw new IllegalArgumentException( "No external properties file name defined with the option" );
                    }
                }
            // Logging without path (option "-log")
            opt = OPTION_PREFIX + LOG_PATH_OPTION_NO_PATH;
            if ( aArgs[ i ].equals( opt ) )
                {
                // No logging file defined
                LogWriter.initialize( null );
                }
            // Logging with path or with option "-log:"
            opt = OPTION_PREFIX + LOG_PATH_OPTION;
            if ( aArgs[ i ].startsWith( opt ) )
                {
                iLogDir = aArgs[ i ].substring( opt.length() );
                if ( iLogDir.length() == 0 )
                    {
                    // No logging file defined
                    LogWriter.initialize( null );
                    }
                else
                    {
                    LogWriter.initialize( new File( iLogDir ) );
                    }
                }
            }
        }
    }
