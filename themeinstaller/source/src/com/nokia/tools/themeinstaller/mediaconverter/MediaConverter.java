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
* Description:  This class is used for converting media files
 *
*/

package com.nokia.tools.themeinstaller.mediaconverter;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import javax.imageio.IIOImage;
import javax.imageio.ImageIO;
import javax.imageio.ImageReader;
import javax.imageio.ImageWriter;
import javax.imageio.stream.ImageInputStream;
import javax.imageio.stream.ImageOutputStream;

import com.nokia.tools.themeinstaller.odtconverter.ConverterProperties;

/**
 * Base class for different MediaConverters
 * Media converters are used for e.g. converting jpg to mbm
 * @author jutarhon
 *
 */
public class MediaConverter
    {
    protected static final String MEDIA_CONVERTER_APPLICATION= "media_converter";
    private static final String WINDOWS_EXCUTABLE_EXTENSION = "exe";
    private static final String LINUX_OS_NAME = "linux";
    private static final String OPERATING_SYSTEM_PROPERTY = "os.name";
    protected static final char SPACE = ' ';
    protected static final char DOT = '.';
    private static final String BMP = "bmp";
    private static final String COLOR_SETTING = "color_setting";
    protected static String DEFAULT_SUCCESS_LINE = "Success.";

    protected ConverterProperties iProperties;
    private Process iProcess;

    protected String iExtraParameters = null;

    /**
     * Default constructor.
     * @throws IOException If loading properties fails
     */
    public MediaConverter() throws IOException
        {
        iProperties = new ConverterProperties();
        }

    /**
     * Returns possible set extra parameters for running converter application
     * or null if not set
     * @return the iExtraParameters
     */
    public String getExtraParameters()
        {
        return iExtraParameters;
        }

    /**
     * Sets extra parameters for running converter application
     * Set null for unsetting
     * @param aExtraParameters Extra parameters to set
     */
    public void setExtraParameters( String aExtraParameters )
        {
        iExtraParameters = aExtraParameters;
        }

    /**
     * Returns command line parameters for specified filenames
     * including the actual executable
     * example: bmconv.exe target.mbm source.jpg
     * @param aFilenames List of filenames to added to command line
     * @param aTargetFile Filename for target bitmap
     * @return Executable parameters
     */
    protected String getExecParameters( List aFilenames, String aTargetFile )
        {
        StringBuffer sb = new StringBuffer();

        // Get the execution location
        URL resource =
                getClass().getProtectionDomain().getCodeSource().getLocation();
        File bin = new File( resource.getPath() );

        // Find the bmconv from the installation directory
        sb.append( bin.getParent() + File.separatorChar );

        // Windows uses bmconv.exe and Linux bmconv
        if ( System.getProperty( OPERATING_SYSTEM_PROPERTY ).equalsIgnoreCase(
                LINUX_OS_NAME ) )
            {
            sb.append( iProperties.getProperty( MEDIA_CONVERTER_APPLICATION ) );
            }
        else
            {
            sb.append( iProperties.getProperty( MEDIA_CONVERTER_APPLICATION )
                    + DOT + WINDOWS_EXCUTABLE_EXTENSION );
            }

        sb.append( SPACE );
        if( iExtraParameters != null )
            {
            sb.append( iExtraParameters );
            sb.append( SPACE );
            }
        sb.append( aTargetFile );
        sb.append( SPACE );
        for ( Iterator iterator = aFilenames.iterator(); iterator.hasNext(); )
            {
            sb.append( iProperties.getProperty( COLOR_SETTING ) );
            sb.append( iterator.next() );
            if( iterator.hasNext() )
                {
                sb.append( SPACE );
                }
            }
        return sb.toString();
        }
    /**
     * Getter for environment variables in form "key=value"
     * To be overwritten in derived class if environment variables are needed
     * @return String array of "key=value" pairs.
     */
    protected String[] getEnvironmentVariables()
        {
        return null;
        }

    /**
     * Returns success line that is excepted in output
     * @return Success line
     */
    protected String getSuccesIndicationLine()
        {
        return DEFAULT_SUCCESS_LINE;
        }

    /**
     * Cancels the executing conversion operation
     */
    public void cancelConversion()
        {
        if( iProcess != null )
            {
            iProcess.destroy();
            }
        }

    /**
     * Converts one ore more files to target file
     * @param aFilenames Files to be converted
     * @param aTargetFile Target file
     * @throws IOException If IO error occurs or tool fails conversion
     */
    public void convertMedia( List aFilenames,
                              String aTargetFile ) throws IOException
        {
        ArrayList newFiles = new ArrayList();

        checkMedias( aFilenames, newFiles );
        Runtime rt = Runtime.getRuntime();
        iProcess = rt.exec( getExecParameters( aFilenames, aTargetFile ),
                                getEnvironmentVariables() );
        try
            {
            iProcess.waitFor();
            }
        catch ( InterruptedException e )
            {
            throw new IOException( "Conversion interrupted" );
            }

        if( iProcess.exitValue() != 0 )
            {
            InputStream input = null;
            BufferedReader in = null;
            StringBuffer sb = null;
            try
                {
                // reading the error logs
                input = iProcess.getErrorStream();
                in = new BufferedReader( new InputStreamReader( input ) );
                sb = new StringBuffer();
                String line = null;
                while ( ( line = in.readLine() ) != null )
                    {
                    sb.append( line );
                    sb.append( '\n' );
                    }
                }
            finally
                {
                if( input != null )
                    {
                    input.close();
                    }
                if( in != null )
                    {
                    in.close();
                    }
                }

            deleteTemporaryFiles( newFiles );
            throw new IOException( "Conversion failed with error code: " +
                                   iProcess.exitValue() +
                                   "\nError log: " + sb.toString() );
            }
        // read the output logs, and check that there is success indication (in case that tool does not
        // support sending error code)
        boolean success = false;
        String line = null;
        String lastLine = null;
        InputStream input = null;
        BufferedReader in = null;
        try
            {
            input = iProcess.getInputStream();
            in = new BufferedReader( new InputStreamReader( input ) );
            while ( ( line = in.readLine() ) != null )
                {
                if( line.equals( getSuccesIndicationLine() ) )
                    {
                    success = true;
                    break;
                    }
                lastLine = line;
                }
            }
        finally
            {
            if( input != null )
                {
                input.close();
                }
            if( in != null )
                {
                in.close();
                }
            }
        iProcess = null;
        // Delete temporary files
        deleteTemporaryFiles( newFiles );
        // did not found success line
        if( !success )
            {
            throw new IOException( "Running media converter failed: " + lastLine );
            }
        }

    /**
     * Delete temporary files
     * @param newFiles List of temporary files
     * @throws IOException If file deletion fails
     */
    protected void deleteTemporaryFiles( List aNewFiles ) throws IOException
        {
        for ( Iterator iterator = aNewFiles.iterator(); iterator.hasNext(); )
            {
            String filename = ( String ) iterator.next();
            File file = new File( filename );
            if( !file.delete() )
                {
                throw new IOException( "Temporary file deletion failed: " + filename );
                }
            }
        }

    /**
     * Checks that input medias does not contain illegal files and converts
     * other image formats to BMP
     * @param aFilenames List of files to be added in MBM file
     * @param aNewFiles List of created temporary files
     * @throws IOException thrown if some of encoders are missing, or some error in image reading/writing
     */
    protected void checkMedias( List aFilenames,
                                List aNewFiles ) throws IOException
        {
        // load BMP writer
        Iterator writers = ImageIO.getImageWritersByFormatName( BMP );
        if( !writers.hasNext() )
            {
            throw new IOException( "BMP encoder not found" );
            }
        ImageWriter bmpWriter = ( ImageWriter ) writers.next();

        ArrayList newNames = new ArrayList();
        // Go through all files and check if there is something else than BMP
        for ( Iterator iterator = aFilenames.iterator();
              iterator.hasNext(); )
            {
            String imageName = ( String ) iterator.next();
            ImageInputStream input = ImageIO.createImageInputStream(
                    new File( imageName ) );

            String destinationImage = null;
            try
                {
                Iterator readers = ImageIO.getImageReaders( input );
                if( !readers.hasNext() )
                    {
                    throw new IOException( "Unknown file" );
                    }
                ImageReader ir = ( ImageReader ) readers.next();
                //Convert file if it is not BMP
                destinationImage = imageName;
                if( !ir.getFormatName().equalsIgnoreCase( BMP ) )
                    {
                    // read original image
                    ir.setInput( input );
                    IIOImage image = ir.readAll( 0, null );
                    destinationImage = imageName.substring(
                            0, imageName.lastIndexOf( DOT ) + 1 ) + BMP;
                    File destFile = new File( destinationImage );
                    int index = 1;
                    // create unique name to not overwrite any existing files
                    while( destFile.exists() )
                        {
                        destinationImage = imageName.substring( 0,
                                           imageName.lastIndexOf( DOT ) )
                                           + index++ + DOT + BMP;
                        destFile = new File( destinationImage );
                        }
                    // Write image back in BMP format
                    ImageOutputStream output =
                            ImageIO.createImageOutputStream( destFile );
                    try
                        {
                        bmpWriter.setOutput( output );
                        bmpWriter.write( image );
                        }
                    finally
                        {
                        if( output != null )
                            {
                            output.close();
                            }
                        }
                    aNewFiles.add( destinationImage );
                    }
                }
            finally
                {
                if( input != null )
                    {
                    input.close();
                    }
                }

            newNames.add( destinationImage );
            }
        // change new names to list
        aFilenames.clear();
        aFilenames.addAll( newNames );
        }
    }
