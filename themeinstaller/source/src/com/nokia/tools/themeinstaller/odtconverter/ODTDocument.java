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
* Description:  This class contains DOM document, ODT header
 *                and ODT resources.
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.util.Vector;
import org.w3c.dom.Document;

/**
 * This class contains DOM document, ODT header and ODT resources.
 */
public class ODTDocument
    {

    /** ODTHeader */
    protected ODTHeader iODTHeader;

    /** Vector for ODTResources */
    protected Vector iODTResources = new Vector();

    /** DOMDocument */
    protected Document iDOMDocument;


    /**
     * Setter for ODTHeader
     * @param aODTHeader
     */
    public void setODTHeader( ODTHeader aODTHeader )
        {
        iODTHeader = aODTHeader;
        }

    /**
     * Getter for ODTHeader
     */
    public ODTHeader getODTHeader()
        {
        return iODTHeader;
        }

    /**
     * Setter for ODTResources
     * @param aODTResources
     */
    public void setODTResources( Vector aODTResources )
        {
        iODTResources = aODTResources;
        }

    /**
     * Getter for ODTResources
     */
    public Vector getODTResources()
        {
        return iODTResources;
        }

    /**
     * Setter for DOMDocument
     * @param aDOMDocument
     */
    public void setDOMDocument( Document aDOMDocument )
        {
        iDOMDocument = aDOMDocument;
        }

    /**
     * Getter for DOMDocument
     */
    public Document getDOMDocument()
        {
        return iDOMDocument;
        }

    }
