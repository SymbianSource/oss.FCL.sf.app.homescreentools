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
* Description: 
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.net.URL;
import java.util.Properties;

/**
 * Properties for ODT to XML converter
 * @author jutarhon
 */
public class ConverterProperties extends Properties
    {
    /**
     * Default serial version UID
     */
    private static final long serialVersionUID = 1L;
    private static final String PROPERTY_FILE =
        "data" + File.separatorChar + "ThemeInstaller.prop";
    private static ConverterProperties sInstance = null;
    private static String sPropFileName = null;

    /**
     * Default constructor, loads the properties from default place
     * @throws IOException If default file is not found or some other IO error occurs
     */
    public ConverterProperties() throws IOException
        {
        // Get the execution location
        URL resource =
                getClass().getProtectionDomain().getCodeSource().getLocation();
        File bin = new File( resource.getPath() );

        // Load properties from the Theme Installation directory
        loadProperties( new File(
                bin.getParent() + File.separatorChar + PROPERTY_FILE ) );
        }

    /**
     * Constructor with specified properties file
     * @param aFile File to read
     * @throws IOException If given file is not found or some other IO error occurs
     */
    public ConverterProperties( File aFile ) throws IOException
        {
        loadProperties( aFile );
        }

    /**
     * Constructor with default values
     * @param aDefaults Default properties values
     * @throws IOException  If default file is not found or some other IO error occurs
     */
    public ConverterProperties( Properties aDefaults ) throws IOException
        {
        super( aDefaults );
        loadProperties( new File( PROPERTY_FILE ) );
        }

    /**
     * Loads the properties from file
     * @param aFile File to read
     * @throws IOException  If given file is not found or some other IO error occurs
     */
    protected void loadProperties( File aFile ) throws IOException
        {
        FileInputStream file = null;
        try
            {
            file = new FileInputStream( aFile );
            load( file );
            }
        finally
            {
            if( file != null )
                {
                file.close();
                }
            }
        }

    /**
     * Singleton method for getting the ConverterProperties instance. Note that
     * the initialize method must be called before this one.
     * @return ConverterProperties instance
     * @throws IllegalStateException if this method has been called before
     * initialize has been called.
     */
    public static ConverterProperties getInstance()
        {
        if( sInstance == null )
            {
            throw new IllegalStateException( "Converter Properties: " +
                    "Initialize must be called before the properties " +
                    "can be used" );
            }

        return sInstance;
        }

    /**
     * Initialize method for constructing and reading the properties. The
     * properties are re-initialized only if the given property file differs
     * from the one used in the previous initialization.
     * @param aPropFile Properties file
     * @throws IOException If required properties can not be read from the
     * property file.
     */
    public static void initialize( File aPropFile )
        throws IOException
        {
        // Already initialized if:
        // sInstance is not null AND
        // sPropFileName equals with aPropFile
        if( sInstance != null &&
          ( sPropFileName != null && aPropFile != null && sPropFileName.equals( aPropFile.getPath() ) ||
          ( sPropFileName == null && aPropFile == null ) ) )
            {
            return;
            }

        // Create a new instance
        if( aPropFile == null )
            {
            sInstance = new ConverterProperties();
            sPropFileName = null;
            }
        else
            {
            sInstance = new ConverterProperties( aPropFile );
            sPropFileName = aPropFile.getPath();
            }
        }
    }
