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
* Description:  Base class for file operations
 *
*/


package com.nokia.tools.themeinstaller.defrep.operations;

import java.io.File;
import java.util.Observable;
import java.util.Observer;

public abstract class FileOperation extends Observable implements Runnable
    {

    // File related to the operation
    protected File iFile;

    // Listener of the operation
    protected Observer iListener;

    /**
     * Called when the operation is finished. Sets the observable object as
     * changed and notifies its observers.
     *
     * @param aFile The file under operation
     * @param aErrorCode Error code
     */
    protected void finished( File aFile, int aErrorCode )
        {
        FileOperationEvent event = new FileOperationEvent( aFile,
                                                           aErrorCode );
        super.setChanged();
        super.notifyObservers( event );
        }
    }
