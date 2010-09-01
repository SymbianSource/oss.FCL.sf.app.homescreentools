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
* Description:  Property value list for style property values.
 *
*/


package com.nokia.tools.themeinstaller.odtconverter;

import java.io.IOException;
import java.util.Enumeration;
import java.util.Vector;

public class PropertyValueList
    {

    // CONSTANTS
    private static int PROPERTY_VALUE_LIST_TYPE = 3;

    // Property item list
    private Vector iList;

    // Reference to the String Pool
    private StringPool iStringPool;

    /**
     * Constructor.
     */
    public PropertyValueList( StringPool aStringPool )
        {
        iStringPool = aStringPool;
        iList = new Vector();
        }

    /**
     * Create a new item and add it to the list.
     * @param aItem The new item
     */
    public PropertyValue newItem()
        {
        PropertyValue propVal = new PropertyValue( iStringPool );
        iList.add( propVal );
        return propVal;
        }

    /**
     * Remove an item from the list.
     * @param aItem Item to remove
     * @return true if the item was removed, otherwise false is returned
     */
    public boolean removeItem( PropertyValue aItem )
        {
        return iList.remove( aItem );
        }

    /**
     * Externalize the list to the stream.
     * @param aStream Target stream
     * @throws IOException if writing to a stream fails
     * @throws ODTException if writing to a stream fails
     */
    public void externalize( ODTDataOutputStream aStream )
        throws ODTException, IOException
        {
        // Write list type - int8
        aStream.writeByte( PROPERTY_VALUE_LIST_TYPE );

        // Write item count - int32
        aStream.writeInt32( iList.size() );

        Enumeration elements = iList.elements();

        // Write all property values
        while( elements.hasMoreElements() )
            {
            PropertyValue propVal = ( PropertyValue ) elements.nextElement();
            propVal.externalize( aStream );
            }
        }


    }
