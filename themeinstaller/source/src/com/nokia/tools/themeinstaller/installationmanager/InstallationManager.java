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
* Description:  Starting point for theme install procedure.
 *
*/


package com.nokia.tools.themeinstaller.installationmanager;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.util.Enumeration;
import java.util.Observable;
import java.util.Observer;
import java.util.Vector;

import javax.xml.transform.Result;
import javax.xml.transform.Source;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.w3c.dom.traversal.NodeIterator;

import com.nokia.tools.themeinstaller.defrep.DefinitionRepository;
import com.nokia.tools.themeinstaller.defrep.IDefinitionRepository;
import com.nokia.tools.themeinstaller.defrep.operations.FileOperation;
import com.nokia.tools.themeinstaller.defrep.operations.FileOperationEvent;
import com.nokia.tools.themeinstaller.odtconverter.ConverterProperties;
import com.nokia.tools.themeinstaller.odtconverter.IParseOperationListener;
import com.nokia.tools.themeinstaller.odtconverter.ODTDocument;
import com.nokia.tools.themeinstaller.odtconverter.ODTHeader;
import com.nokia.tools.themeinstaller.odtconverter.ODTInputStream;
import com.sun.org.apache.xpath.internal.XPathAPI;

/**
 * Installation Manager class is the starting point for the theme installation
 * procedure.
 */
public class InstallationManager implements Observer, IInstallationListener
    {

    protected static final String MANIFEST_SUFFIX = ".dat";

    // Theme manifest file
    private File iManifest;

    // Destination root directory
    private File iDestinationDir;

    // Definition repository for file operations
    private IDefinitionRepository iDefRep;

    // Data directory containing the theme to install
    private String iDataDir;

    // Installation observer
    private IInstallationListener iListener;

    // Resource installer
    private IResourceInstaller iResourceInstaller;

    // Installation list of ongoing installations
    private InstallationList iList;

    // Lock for asynchronous operations.
    private Lock iLock;

    // Lock for multi theme installs
    private Lock iMultiThemeLock;

    // Localisation settings
    private File iLocSettings;
    
    //DTD may contain some errors such as missing semicolon. Set
    //this to true if these are to be fixed. Currently passed via 
    //argument.
    private static boolean fixDTD = false;

    /**
     * Default constructor
     * @param aParams Installation parameters
     * @param aListener Installation observer
     * @throws IOException if Resource Installer can not be created
     */
    public InstallationManager( InstallationParameters aParams,
                                IInstallationListener aListener )
        throws IOException
        {
        // Properties must be initialized before using them
        ConverterProperties.initialize( aParams.getPropFile() );

        iManifest = aParams.getManifest();
        iLocSettings = aParams.getLocSettings();
        iDestinationDir = aParams.getDestinationDir();
        iListener = aListener;

        // Create destination directory structure
        if( !iDestinationDir.exists() )
            {
            iDestinationDir.mkdirs();
            }

        iDefRep = DefinitionRepository.getInstance();

        if( iManifest.getParent() == null )
            {
            iDataDir = ManifestFactory.CURRENT_DIR + File.separatorChar;
            }
        else
            {
            iDataDir = iManifest.getParent() + File.separatorChar;
            }

        iResourceInstaller =
            new ResourceInstaller( iDefRep, iDestinationDir, iDataDir);
        iList = new InstallationList();
        iLock = new Lock();
        iMultiThemeLock = new Lock();
        }

    
    public static boolean isFixDTD() {
		return fixDTD;
	}


	public static void setFixDTD(boolean fixDTD) {
		InstallationManager.fixDTD = fixDTD;
	}


	/**
     * Starts the actual installation
     * Progress will be informed via listener
     * @throws IOException If files cannot be found, or new files cannot be written
     * @throws IllegalArgumentException If there exists syntax errors in manifest file
     */
    public void startInstallation() throws IOException
        {
        // Source parameter is a directory
        if( iManifest.isDirectory() )
            {
            Enumeration manifests = searchManifests( iManifest ).elements();
            if( manifests.hasMoreElements() )
                {
                // Install all found themes
                installMultiTheme( manifests );
                }
            else
                {
                // No themes found
                throw new IllegalArgumentException(
                        "Manifest files not found from: " + iManifest.getPath() );
                }
            }
        // Source parameter is a file
        else
            {
            // Parse the manifest
            ManifestFactory factory = new ManifestFactory( iLocSettings );
            IThemeManifest manifest = factory.createManifest( iManifest );

            // Install sub themes of a multi theme manifest, if any
            Enumeration manifests = manifest.getManifestFiles().elements();
            if( manifests.hasMoreElements() )
                {
                installMultiTheme( manifests );
                }
            // Install a normal theme
            else
                {
                installTheme( manifest, iLocSettings );
                }
            }
        }

    /* (non-Javadoc)
     * @see java.util.Observer#update(java.util.Observable, java.lang.Object)
     */
    public void update( Observable aObservable, Object aEvent )
        {
        // Language install event
        if( aObservable instanceof LanguageInstaller )
            {
            // Notify that the parsing operation has completed and
            // the install of next language variant will start
            iLock.unLock();

            LanguageInstallEvent event = ( LanguageInstallEvent )aEvent;
            ODTHeader header = event.getODTDocument().getODTHeader();
            ProgressEvent pe = new ProgressEvent();
            pe.setState( IInstallationListener.STATE_PARSED );
            pe.setName( ( String )header.get( ODTHeader.ThemeShortName ) );
            pe.setLanguage( (
                    ( Integer )header.get( ODTHeader.Language ) ).intValue() );
            pe.setError( event.getErrorCode(), event.getReason() );

            iListener.installationProgress( pe );
            if( event.getErrorCode() ==
                IParseOperationListener.OPERATION_SUCCESSFUL )
                {
                InputStream in = null;
                try
                    {
                    // Store the ODT file
                    ODTDocument document = event.getODTDocument();
                    in = new ODTInputStream( document );
                    
//                    Source s = new DOMSource(document.getDOMDocument());
//                    
//                    Result r = new StreamResult(new File("C://output.xml"));
//                    
//                    Transformer t = TransformerFactory.newInstance().newTransformer();
//                    
//                    t.transform(s, r);
                    	
                    iDefRep.storeODT( iDestinationDir,
                            document.getODTHeader(),
                            in,
                            this );
                    }
                catch ( Exception e )
                    {
                    pe.setError( IInstallationListener.ERROR, e.toString() );
                    iListener.installationCompleted( pe );
                    }
                finally
                    {
                    if( in != null )
                        {
                        try
                            {
                            in.close();
                            }
                        catch ( IOException e )
                            {
                            // Ignore error
                            }
                        }
                    }
                }
            else
                {
                pe.setError( event.getErrorCode(), event.getReason() );
                iListener.installationCompleted( pe );
                }
            }
        // File operation event
        else if( aObservable instanceof FileOperation )
            {
            FileOperationEvent event = ( FileOperationEvent )aEvent;
            ProgressEvent pe = new ProgressEvent();
            pe.setState( IInstallationListener.STATE_WRITED );
            pe.setFileName( event.getFullDestPath() );
            pe.setError( event.getErrorCode(), null );

            if( event.getErrorCode() == FileOperationEvent.OPERATION_SUCCESSFUL )
                {
                pe.setFileName( event.getFullDestPath() );
                iListener.installationProgress( pe );
                }
            else
                {
                pe.setError( event.getErrorCode(), null );
                iListener.installationCompleted( pe );
                }

            iList.removeInstall( event.getDestPath() );
            if( !iList.installsExist() )
                {
                pe.setError( event.getErrorCode(), null );
                iListener.installationCompleted( pe );
                }
            }
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IInstallationListener#installationProgress(com.nokia.tools.themeinstaller.installationmanager.ProgressEvent)
     */
    public void installationProgress( ProgressEvent aEvent )
        {
        // Pass the event
        iListener.installationProgress( aEvent );
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.installationmanager.IInstallationListener#installationCompleted(com.nokia.tools.themeinstaller.installationmanager.ProgressEvent)
     */
    public void installationCompleted( ProgressEvent aEvent )
        {
        // Pass the event and release the multi theme install lock
        iListener.installationCompleted( aEvent );
        iMultiThemeLock.unLock();
        }

    /**
     * Install a normal theme
     * @param aManifest Manifest file
     * @throws IOException if resource files can not be installed
     */
    private void installTheme( IThemeManifest aManifest, File aLocSettings )
        throws IOException
        {
        // Create unlocalized header for copying language independent resources
        ODTHeader unlocalizedHeader =
            LanguageInstaller.createHeader( aManifest, null );
        Vector resources = aManifest.getResources();
        Vector odtResources =
            iResourceInstaller.installResources( resources, unlocalizedHeader );

        // Get all languages
        Enumeration languages =
            aManifest.getLanguages().elements();

        // Install each language variant
        while( languages.hasMoreElements() )
            {
            LanguageSpecificData language =
                ( LanguageSpecificData )languages.nextElement();
            LanguageInstaller installer = new LanguageInstaller(
                    this, aManifest, language, aLocSettings, iResourceInstaller );

            // Add language id to the log
            iList.addInstall( language.getLanguageId() );

            // Add language independent resources
            installer.addResources( odtResources );

            try
                {
                // Start the installation process
                installer.install();

                // Wait for the parsing process to complete
                iLock.lock();
                }
            catch( Exception e )
                {
                // In error cases, cancel the installation
                ProgressEvent pe = new ProgressEvent();
                pe.setName( aManifest.getThemeShortName() );
                pe.setLanguage( language.getLanguageId().intValue() );
                pe.setError( IInstallationListener.ERROR, e.toString() );
                iListener.installationCompleted( pe );
                }
            }
        }

    /**
     * Install sub themes of a multi theme manifest.
     * @param aManifests List of manifests
     */
    private void installMultiTheme( Enumeration aManifests )
        {
        while( aManifests.hasMoreElements() )
            {
            File f = ( File )aManifests.nextElement();
            try
                {
                // Create installation parameters for the new
                // Installation Manager instance
                InstallationParameters params = new InstallationParameters(
                        f, iDestinationDir );
                params.setLocSettings( iLocSettings );

                // Create a new installation manager
                InstallationManager i = new InstallationManager( params, this );
                i.startInstallation();

                // Install only a theme at a time
                iMultiThemeLock.lock();
                }
            catch ( Exception e )
                {
                // In error cases, cancel the installation
                ProgressEvent pe = new ProgressEvent();
                pe.setFileName( f.getPath() );
                pe.setError( IInstallationListener.ERROR,
                        "Sub theme installation failed: " + e.toString() );
                iListener.installationCompleted( pe );
                }
            }

        }

    private Vector searchManifests( File aLocation )
        {
        // Create a FilenameFilter class for searching manifest (.dat) files
        FilenameFilter filter = new FilenameFilter()
            {
            public boolean accept( File aDir, String aName )
                {
                if( aName.endsWith( MANIFEST_SUFFIX ) )
                    {
                    return true;
                    }
                return false;
                }
            };

        // List all manifest files in the directory and add them to
        // the result vector
        File[] files = aLocation.listFiles( filter );
        Vector v = new Vector();
        for( int i = 0; i < files.length; i++ )
            {
            v.add( files[ i ] );
            }

        return v;
        }

    }
