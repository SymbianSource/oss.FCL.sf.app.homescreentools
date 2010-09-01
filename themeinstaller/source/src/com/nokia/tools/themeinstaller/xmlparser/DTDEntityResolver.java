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
* Description:  Entity Resolver for using external DTD files in XML parsing.
 *
*/


package com.nokia.tools.themeinstaller.xmlparser;

import java.io.IOException;

import org.xml.sax.EntityResolver;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

/**
 * DTD Entity Resolver is for using external DTD files in XML parsing.
 * The resolveEntity method returns null if the provided system id does
 * not end with the ".dtd".
 */
public class DTDEntityResolver implements EntityResolver
    {

    // CONSTANTS
    // DTD file extension
    private static final String DTD_FILE_EXT = ".dtd";

    // File name of the external DTD
    private String iFileName;

    /**
     * Constructor.
     * @param aFileName file name of the DTD file
     */
    public DTDEntityResolver( String aFileName )
        {
        iFileName = aFileName;
        }

    /* (non-Javadoc)
     * @see org.xml.sax.EntityResolver#resolveEntity(java.lang.String, java.lang.String)
     */
    public InputSource resolveEntity( String aPublicId, String aSystemId )
            throws SAXException, IOException
        {
        DTDInputSource is = null;

        // For DTD files, provide input source containing the external DTD for
        // the XML parser
        if( aSystemId.endsWith( DTD_FILE_EXT ) )
            {
            is = new DTDInputSource( iFileName );
            }

        return is;
        }

    }
