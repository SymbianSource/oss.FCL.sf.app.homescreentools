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
* Description:  This class stores parser components
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.io.IOException;
import java.util.Vector;

/**
 * This class stores parser components and calls components parse method.
 */
public class ParserComposite extends ParseOperation
                                implements IParseOperationListener
    {

    /** Vector for parsing operations */
    Vector iParseOperations = new Vector();

    /** Vector element index */
    private int iIndex = 0;

    /**
     * Instantiates a new ParserComposite.
     */
    public ParserComposite()
        {
        }

    /**
     * Adds parsers to ParserComposite.
     *
     * @param ParseOperation
     */
    public void addOperation( ParseOperation aParseOperation )
        {
        iParseOperations.addElement( aParseOperation );
        aParseOperation.addListener( this );
        }

    /**
     * If parse operation was successful, calls next until all available files
     * are parsed
     */
    public void parseOperationCompleted( int aErr, String aReason )
        {
        ParseOperation oper;
        if( aErr == OPERATION_SUCCESSFUL )
            {
            // get DOM document from previous parse operation
            oper = ( ParseOperation )iParseOperations.elementAt( iIndex++ );
            iDOMDocument = oper.getDOMDocument();

            if( iIndex < iParseOperations.size() )
                {
                oper =
                     ( ParseOperation )iParseOperations.elementAt( iIndex );
                try
                    {
                    oper.iDOMDocument = iDOMDocument;
                    oper.parse( );
                    }
                catch ( IOException e )
                    {
                    operationCompleted( SYNTAX_ERROR, e.getMessage() );
                    }
                catch ( ODTException e )
                    {
                    operationCompleted( SYNTAX_ERROR, e.getMessage() );
                    }
                }
            else
                {
                operationCompleted( OPERATION_SUCCESSFUL, null );
                }
            }
        else
            {
            operationCompleted( aErr, aReason );
            }
        }

    /* (non-Javadoc)
     * @see com.nokia.tools.themeinstaller.odtconverter.ParseOperation#parse()
     */
    public void parse( )
            throws IOException, ODTException
        {
        iIndex = 0;

        if( !iParseOperations.isEmpty() )
            {
            ParseOperation oper =
                       ( ParseOperation )iParseOperations.elementAt( iIndex );
            oper.parse( );
            }
        else
            {
            return;
            }
        }
    }
