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
* Description:  Class for parsing operations
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.io.IOException;
import java.util.Enumeration;
import java.util.Vector;

import org.w3c.dom.Document;

/**
 * This class provides a skeletal implementation of parsing operation
 */
public abstract class ParseOperation
    {

    /** Listener for parsing operations */
    IParseOperationListener iListener;

    /** All listeners */
    Vector iListeners = new Vector();

    /** DOM document */
    protected Document iDOMDocument;

    /**
     * Parses file to DOM Document.
     *
     * @throws IOException Signals that an I/O exception has occurred.
     * @throws ODTException the ODT exception
     */
    public abstract void parse( )
            throws IOException, ODTException;

    /**
     * Getter for DOM document
     * @return DOM document
     */
    public Document getDOMDocument()
        {
        return iDOMDocument;
        }

    /**
     * Adds the listener.
     * @param aListener IParseOperationListener
     */
    public void addListener( IParseOperationListener aListener )
        {
        iListeners.addElement( aListener );
        }

    /**
     * Calls OperationCompleted for all listeners
     * @param aErr
     * @param aReason
     */
    public void operationCompleted( int aErr, String aReason )
        {
        for ( Enumeration e = iListeners.elements(); e.hasMoreElements(); )
            {
            IParseOperationListener listener = ( IParseOperationListener ) e
                    .nextElement();
            listener.parseOperationCompleted( aErr, aReason );
            }
        }

    }
