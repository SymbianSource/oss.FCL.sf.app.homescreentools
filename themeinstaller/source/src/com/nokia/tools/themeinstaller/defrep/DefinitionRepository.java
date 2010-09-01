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
 * Description:  Definition Repository implementation
 *
 */

package com.nokia.tools.themeinstaller.defrep;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.Observer;

import com.nokia.tools.themeinstaller.odtconverter.ConverterProperties;
import com.nokia.tools.themeinstaller.odtconverter.ODTHeader;
import com.nokia.tools.themeinstaller.odtconverter.ThemeStatusResolver;
import com.nokia.tools.themeinstaller.defrep.operations.CopyOperation;
import com.nokia.tools.themeinstaller.defrep.operations.FileOperation;
import com.nokia.tools.themeinstaller.defrep.operations.StoreOperation;

/**
 * Definition repository class.
 */
public class DefinitionRepository implements IDefinitionRepository {

	// CONSTANTS
	// Property keys
	private static final String THEMES_ROOT_ROM = "themes_datacage_rom";
	private static final String THEMES_ROOT_USER_DISC = "themes_datacage_user_disc";
	private static final String ODT_FILE_EXT_FORMAT = "odt_file_ext_format";
	private static final String ODT_RESOURCES_FOLDER = "odt_resources_folder";
	private static final String ODT_LANG_RESOURCES_FOLDER = "odt_lang_resources_folder";

	// Singleton instance
	private static DefinitionRepository sInstance = null;

	/**
	 * Definition repository private constructor.
	 */
	private DefinitionRepository() {
	}

	/**
	 * Get a Definition Repository instance (singleton).
	 * 
	 * @return Definition Repository instance
	 */
	public static DefinitionRepository getInstance() {
		if (sInstance == null) {
			sInstance = new DefinitionRepository();
		}

		return sInstance;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * com.nokia.tools.odtconverter.defrep.IDefinitionRepository#copy(java.lang
	 * .String, java.util.Observer)
	 */
	public void copy(File aSource, File aDestination, boolean aAppend,
			Observer aListener) {
		CopyOperation operation = new CopyOperation(aSource, aDestination,
				aAppend);
		operation.addObserver(aListener);
		performOperation(operation);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * com.nokia.tools.odtconverter.defrep.IDefinitionRepository#store(java.
	 * lang.String, java.io.InputStream, java.util.Observer)
	 */
	public void store(File aDestination, InputStream aStream, Observer aListener) {
		StoreOperation operation = new StoreOperation(aDestination, aStream);
		operation.addObserver(aListener);
		performOperation(operation);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * com.nokia.tools.odtconverter.defrep.IDefinitionRepository#storeODT(java
	 * .io.File, com.nokia.tools.odtconverter.ODTDocument, java.util.Observer)
	 */
	public void storeODT(File aDestination, ODTHeader aHeader,
			InputStream aStream, Observer aListener) throws IOException {
		File destination = new File(createODTPath(aDestination, aHeader));
		store(destination, aStream, aListener);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * com.nokia.tools.odtconverter.defrep.IDefinitionRepository#copyResource
	 * (java.io.File, java.io.File, com.nokia.tools.odtconverter.ODTHeader,
	 * java.util.Observer)
	 */
	public void copyResource(File aSource, File aDestination,
			ODTHeader aHeader, Observer aListener) throws IOException {
		ConverterProperties properties = ConverterProperties.getInstance();
		StringBuffer odtPath = combineDirectory(aDestination, aHeader,
				properties);

		// Get the language to resolve the destination directory
		Integer language = (Integer) aHeader.get(ODTHeader.Language);
		if (language != null) {
			// Location for language specific resources
			String template = properties.getProperty(ODT_LANG_RESOURCES_FOLDER);

			Integer[] formatArguments = { language };
			odtPath.append(String.format(template, formatArguments));
		} else {
			// Location for language independent resources
			odtPath.append(properties.get(ODT_RESOURCES_FOLDER));
		}

		odtPath.append(aSource.getName());
		File destFile = new File(odtPath.toString());
		copy(aSource, destFile, false, aListener);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * com.nokia.tools.odtconverter.defrep.IDefinitionRepository#createODTPath
	 * (java.lang.String, com.nokia.tools.odtconverter.ODTHeader,
	 * com.nokia.tools.odtconverter.ConverterProperties)
	 */
	public String createODTPath(File aDestination, ODTHeader aHeader) {
		// Get themes installation directory from the properties
		ConverterProperties properties = ConverterProperties.getInstance();

		StringBuffer odtPath = combineDirectory(aDestination, aHeader,
				properties);

		// Append ODT file name
		odtPath.append(aHeader.get(ODTHeader.ThemeShortName));

		// Append extension according to the language
		String format = properties.getProperty(ODT_FILE_EXT_FORMAT);
		Integer[] formatArguments = { (Integer) aHeader.get(ODTHeader.Language) };
		odtPath.append(String.format(format, formatArguments));

		return odtPath.toString();
	}

	/**
	 * Combine the installation directory structure. According to the Xuikon,
	 * the destination directory for locked themes is ROM location. Other themes
	 * are stored to the user disk. Rest of the path is determined by theme
	 * details: Application UID, Provider UID, Theme UID and Theme Version.
	 * 
	 * @param aDestination
	 *            destination root directory, usually the epoc root
	 * @param aHeader
	 *            ODT file header
	 * @param aProperties
	 *            converter properties instance
	 * @return complete destination path name for the installed theme
	 */
	private StringBuffer combineDirectory(File aDestination, ODTHeader aHeader,
			ConverterProperties aProperties) {
		StringBuffer odtPath = new StringBuffer();
		odtPath.append(aDestination.getPath());

		// Add file separator only if the destination directory does not
		// already end with the separator
		if (!aDestination.getPath().endsWith(File.separator)) {
			odtPath.append(File.separator);
		}

		// if EXnThemeStatusLicenceeDefault flag is set,
		// theme is installed to ROM (z:\) otherwise to user disc (c:\)
		if ((((Integer) aHeader.get(ODTHeader.Flags)).intValue() & ThemeStatusResolver.E_XN_THEME_STATUS_LICENCEE_DEFAULT) != 0) {
			odtPath.append(aProperties.getProperty(THEMES_ROOT_ROM));
		} else {
			odtPath.append(aProperties.getProperty(THEMES_ROOT_USER_DISC));
		}

		//Bypass adding appuid etc, if we don't have these properties
		if (aHeader.get(ODTHeader.ApplicationUID) != null && aHeader.get(ODTHeader.ProviderUID)!= null
				&&  aHeader.get(ODTHeader.ThemeUID) != null && aHeader.get(ODTHeader.ThemeVersion) != null){
			// Append Application UID
			odtPath.append(((Long) aHeader.get(ODTHeader.ApplicationUID))
					.longValue());
		
			odtPath.append(File.separator);

			// Append Provider UID
			odtPath.append(((Long) aHeader.get(ODTHeader.ProviderUID))
					.longValue());
			odtPath.append(File.separator);

			// Append Theme UID
			odtPath
					.append(((Long) aHeader.get(ODTHeader.ThemeUID))
							.longValue());
			odtPath.append(File.separator);

			// Append Theme version
			odtPath.append(aHeader.get(ODTHeader.ThemeVersion));
			odtPath.append(File.separator);
		}
		return odtPath;
	}

	/**
	 * Start a file operation in a new thread.
	 * 
	 * @param aOperation
	 *            The operation to start.
	 */
	private void performOperation(FileOperation aOperation) {
		Thread thread = new Thread(aOperation);
		thread.start();
	}

}
