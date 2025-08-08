#!/usr/bin/env python3
"""
Visual PDF Splitter Desktop Application with Drag & Drop Page Reordering
A modern GUI tool for splitting PDF files with visual page thumbnails, reordering capability,
folder support, multi-PDF navigation, and crop preview panel
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
import PyPDF2
import os
import zipfile
import io
from PIL import Image, ImageTk
import pymupdf as fitz  # Updated import for PyMuPDF 1.26.3
from pathlib import Path
import threading
from typing import List, Tuple, Optional
import math
import glob
import time

class VisualPDFSplitterApp:
    # UI Constants
    FONT_FAMILY = 'Segoe UI'
    STYLE_SUBTITLE = 'Subtitle.TLabel'
    STYLE_ACCENT_BUTTON = 'Accent.TButton'
    
    # Event constants
    EVENT_BUTTON_1 = '<Button-1>'
    EVENT_CONFIGURE = '<Configure>'
    EVENT_MOUSE_WHEEL = '<MouseWheel>'
    EVENT_BUTTON_4 = '<Button-4>'
    EVENT_BUTTON_5 = '<Button-5>'
    
    def __init__(self, root):
        self.root = root
        self.root.title("Visual PDF Splitter - Page Preview, Selection & Edit Mode")
        self.root.geometry("1600x900")  # Increased width for crop preview panel
        self.root.minsize(1200, 700)
        
        # App state
        self.pdf_document = None
        self.pdf_path = None
        
        # New: Multiple PDF support
        self.pdf_list = []  # List of PDF file paths
        self.current_pdf_index = 0  # Current PDF being viewed
        self.pdf_documents = {}  # Cache for opened PDF documents
        
        self.page_thumbnails = []
        self.selected_ranges = []
        self.current_selection = {'start': None, 'end': None}
        self.thumbnail_size = 150
        self.max_zoom = 1600  # Increased from 800 to 1600
        self.min_zoom = 100
        self.zoom_step = 50
        self.page_widgets = []  # Store page widget references
        self.view_mode = 'grid'  # Default view mode
        
        # NEW: Page editing system (reordering and deletion)
        self.page_order = []  # Stores the current order of pages [0, 1, 2, ...] initially
        self.edit_mode = False  # Toggle for edit mode (reorder + delete + rotate)
        self.deleted_pages = set()  # Set of deleted page indices (0-based)
        self.drag_data = None  # Stores drag information
        self.drop_indicator = None  # Visual drop indicator
        self.drag_ghost = None  # Ghost image during drag
        self.original_order = []  # Backup of original order
        self.original_rotations = {}  # Backup of original rotations
        self.page_rotations = {}  # Current page rotations (page_number: angle)
        self.has_edited = False  # Flag to track if pages have been edited (reordered/deleted)
        
        # New: Crop functionality
        self.crop_mode = False
        self.crop_rectangles = {}  # Store crop rectangles per page: {page_num: [rectangles]}
        self.crop_thumbnails = {}  # Store crop thumbnail images: {crop_id: PhotoImage}
        self.crop_counter = 0  # Counter for unique crop IDs
        self.current_crop = None  # Current crop being drawn
        self.crop_start_pos = None
        self.crop_canvas_items = {}  # Canvas items for crop rectangles
        self.crop_overlay = None  # Current crop overlay rectangle
        self.crop_overlay_canvas = None  # Canvas for crop overlay
        
        # Merge functionality
        self.is_merged_pdf = False  # Flag to track if current PDF is a merged result
        self.merged_temp_path = None  # Path to temporary merged PDF file
        self.merged_first_pdf_name = None  # Name of the first PDF used in merge for default naming
        
        # Per-PDF modification tracking
        self.pdf_modifications = {}  # Dict: {original_path: {'temp_path': str, 'original_path': str}}
        
        # Colors for selection states
        self.colors = {
            'normal': '#f0f0f0',
            'hover': '#e0e0ff',
            'start': '#90EE90',
            'end': '#FFB6C1', 
            'selected': '#FFFF99',
            'border_start': '#008000',
            'border_end': '#FF0000',
            'border_selected': '#FFA500',
            'drag_source': '#FFA500',  # Orange for page being dragged
            'drop_zone': '#87CEEB',    # Sky blue for valid drop zones
            'edit_mode': '#E6E6FA',    # Lavender background in edit mode
            'deleted': '#FFB6C1'       # Light pink for deleted pages
        }
        
        # Setup GUI
        self.setup_styles()
        self.create_widgets()
        self.create_menu()
        
    def setup_styles(self):
        """Configure modern styling"""
        style = ttk.Style()
        style.theme_use('clam')
        
        # Configure custom styles
        style.configure('Title.TLabel', font=(self.FONT_FAMILY, 18, 'bold'))
        style.configure(self.STYLE_SUBTITLE, font=(self.FONT_FAMILY, 11))
        style.configure('Success.TLabel', foreground='green', font=(self.FONT_FAMILY, 10, 'bold'))
        style.configure('Error.TLabel', foreground='red', font=(self.FONT_FAMILY, 10, 'bold'))
        style.configure(self.STYLE_ACCENT_BUTTON, font=(self.FONT_FAMILY, 10, 'bold'))
        style.configure('Edit.TButton', font=(self.FONT_FAMILY, 10, 'bold'), foreground='darkblue')
        
    def create_menu(self):
        """Create application menu"""
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)
        
        # File menu
        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="Open PDF...", command=self.load_pdf, accelerator="Ctrl+O")
        file_menu.add_command(label="Open Folder...", command=self.load_pdf_folder, accelerator="Ctrl+Shift+O")
        file_menu.add_separator()
        file_menu.add_command(label="Merge Two PDFs...", command=self.merge_two_pdfs, accelerator="Ctrl+M")
        file_menu.add_command(label="Merge with External PDF...", command=self.merge_add_external, accelerator="Ctrl+Shift+M")
        file_menu.add_separator()
        file_menu.add_command(label="Clear Selection", command=self.clear_selection, accelerator="Ctrl+C")
        file_menu.add_command(label="Reset Edit Session", command=self.reset_edit_session, accelerator="Ctrl+R")
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.root.quit, accelerator="Ctrl+Q")
        
        # View menu
        view_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="View", menu=view_menu)
        view_menu.add_command(label="Zoom In", command=self.zoom_in, accelerator="Ctrl++")
        view_menu.add_command(label="Zoom Out", command=self.zoom_out, accelerator="Ctrl+-")
        view_menu.add_command(label="Reset Zoom", command=self.reset_zoom, accelerator="Ctrl+0")
        view_menu.add_separator()
        view_menu.add_command(label="Previous PDF", command=self.previous_pdf, accelerator="Up")
        view_menu.add_command(label="Next PDF", command=self.next_pdf, accelerator="Down")
        view_menu.add_separator()
        view_menu.add_command(label="Toggle Crop Mode", command=self.toggle_crop_mode, accelerator="Ctrl+T")
        view_menu.add_command(label="Toggle Edit Mode", command=self.toggle_edit_mode, accelerator="Ctrl+E")
        view_menu.add_separator()
        view_menu.add_command(label="Zoom with Mouse Wheel", state='disabled', accelerator="Ctrl+Wheel")
        
        # Tools menu
        tools_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Tools", menu=tools_menu)
        tools_menu.add_command(label="Extract Crops as PDF", command=self.extract_crops_pdf, accelerator="Ctrl+P")
        tools_menu.add_command(label="Extract Crops as PNG", command=self.extract_crops_png, accelerator="Ctrl+G")
        tools_menu.add_command(label="Clear All Crops", command=self.clear_all_crops)
        tools_menu.add_separator()
        tools_menu.add_command(label="Save Edited PDF", command=self.save_edited_pdf, accelerator="Ctrl+S")
        
        # Help menu
        help_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label="How to Use", command=self.show_help, accelerator="F1")
        help_menu.add_command(label="About", command=self.show_about)
        
        # Keyboard shortcuts
        self.root.bind('<Control-o>', lambda e: self.load_pdf())
        self.root.bind('<Control-Shift-O>', lambda e: self.load_pdf_folder())
        self.root.bind('<Control-m>', lambda e: self.merge_two_pdfs())
        self.root.bind('<Control-Shift-M>', lambda e: self.merge_add_external())
        self.root.bind('<Control-c>', lambda e: self.clear_selection())
        self.root.bind('<Control-r>', lambda e: self.reset_edit_session())
        self.root.bind('<Control-q>', lambda e: self.root.quit())
        self.root.bind('<Control-plus>', lambda e: self.zoom_in())
        self.root.bind('<Control-minus>', lambda e: self.zoom_out())
        self.root.bind('<Control-0>', lambda e: self.reset_zoom())
        self.root.bind('<F1>', lambda e: self.show_help())
        
        # New crop shortcuts
        self.root.bind('<Control-t>', lambda e: self.toggle_crop_mode())
        self.root.bind('<Control-p>', lambda e: self.extract_crops_pdf())
        self.root.bind('<Control-g>', lambda e: self.extract_crops_png())
        
        # New edit shortcuts
        self.root.bind('<Control-e>', lambda e: self.toggle_edit_mode())
        self.root.bind('<Control-s>', lambda e: self.save_edited_pdf())
        
        # Arrow key navigation: Left/Right for PDF files, Up/Down for page scrolling
        self.root.bind('<Left>', lambda e: self.handle_left_arrow(e))
        self.root.bind('<Right>', lambda e: self.handle_right_arrow(e))
        self.root.bind('<Up>', lambda e: self.handle_up_arrow(e))
        self.root.bind('<Down>', lambda e: self.handle_down_arrow(e))
        
        # Focus management for keyboard events - ensure root can receive key events
        self.root.focus_set()
        self.root.focus_force()
        
        # Make root focusable and ensure it can receive keyboard events
        self.root.bind('<Button-1>', lambda e: self.root.focus_set())
        
    def handle_left_arrow(self, event):
        """Handle left arrow key - navigate to previous PDF"""
        self.previous_pdf()
        return "break"  # Prevent event propagation
        
    def handle_right_arrow(self, event):
        """Handle right arrow key - navigate to next PDF"""
        self.next_pdf()
        return "break"  # Prevent event propagation
        
    def handle_up_arrow(self, event):
        """Handle up arrow key - scroll up in current PDF"""
        self.scroll_pages(-1)
        return "break"  # Prevent event propagation
        
    def handle_down_arrow(self, event):
        """Handle down arrow key - scroll down in current PDF"""
        self.scroll_pages(1)
        return "break"  # Prevent event propagation
        
    def create_widgets(self):
        """Create main application widgets"""
        # Main container
        main_frame = ttk.Frame(self.root, padding="10")
        main_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        # Configure grid weights
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)
        main_frame.columnconfigure(0, weight=1)
        main_frame.rowconfigure(2, weight=1)
        
        # Header section
        self.create_header(main_frame)
        
        # Control panel
        self.create_control_panel(main_frame)
        
        # Main content area with paned window
        self.create_content_area(main_frame)
        
        # Progress bar (initially hidden)
        self.progress_var = tk.DoubleVar()
        self.progress_bar = ttk.Progressbar(main_frame, variable=self.progress_var, 
                                          maximum=100, mode='determinate')
        
    def create_header(self, parent):
        """Create header section"""
        header_frame = ttk.Frame(parent)
        header_frame.grid(row=0, column=0, sticky=(tk.W, tk.E), pady=(0, 15))
        header_frame.columnconfigure(1, weight=1)
        
        # Title and logo
        title_frame = ttk.Frame(header_frame)
        title_frame.grid(row=0, column=0, sticky=tk.W)
        
        title_label = ttk.Label(title_frame, text="📄 Visual PDF Splitter", style='Title.TLabel')
        title_label.pack(side=tk.LEFT)
        
        subtitle_label = ttk.Label(title_frame, text="Click pages to select • Edit mode for reorder/delete/rotate • Ctrl+wheel to zoom • Visual crop feedback", 
                                  style=self.STYLE_SUBTITLE, foreground='gray')
        subtitle_label.pack(side=tk.LEFT, padx=(15, 0))
        
        # Status
        self.status_var = tk.StringVar(value="Ready - Load a PDF or folder to begin")
        status_label = ttk.Label(header_frame, textvariable=self.status_var, 
                                style=self.STYLE_SUBTITLE, anchor=tk.E)
        status_label.grid(row=0, column=1, sticky=(tk.E, tk.W))
        
    def create_control_panel(self, parent):
        """Create responsive control panel with flexible layout"""
        control_frame = ttk.LabelFrame(parent, text="🎛️ Controls", padding="10")
        control_frame.grid(row=1, column=0, sticky=(tk.W, tk.E), pady=(0, 15))
        control_frame.columnconfigure(0, weight=1)
        
        # Main container for all controls - will wrap as needed
        main_controls_frame = ttk.Frame(control_frame)
        main_controls_frame.pack(fill=tk.X)
        
        # === FILE OPERATIONS SECTION ===
        file_section = ttk.Frame(main_controls_frame)
        file_section.pack(side=tk.LEFT, padx=(0, 20), pady=5)
        
        ttk.Button(file_section, text="📁 Open PDF", 
                  command=self.load_pdf, style=self.STYLE_ACCENT_BUTTON).pack(side=tk.LEFT, padx=(0, 5))
        
        ttk.Button(file_section, text="📂 Open Folder", 
                  command=self.load_pdf_folder, style=self.STYLE_ACCENT_BUTTON).pack(side=tk.LEFT)
        
        # === MERGE SECTION ===
        merge_section = ttk.Frame(main_controls_frame)
        merge_section.pack(side=tk.LEFT, padx=(0, 20), pady=5)
        
        ttk.Label(merge_section, text="Merge:", style=self.STYLE_SUBTITLE).pack(anchor=tk.W)
        
        merge_buttons = ttk.Frame(merge_section)
        merge_buttons.pack()
        
        ttk.Button(merge_buttons, text="🔗 Two PDFs", command=self.merge_two_pdfs).pack(side=tk.LEFT, padx=(0, 2))
        ttk.Button(merge_buttons, text="➕ Add PDF", command=self.merge_add_external).pack(side=tk.LEFT, padx=(0, 2))
        
        # Save Merged PDF button (initially hidden)
        self.save_merged_btn = ttk.Button(merge_buttons, text="💾 Save Merged", command=self.save_merged_pdf, style='Accent.TButton')
        
        # === NAVIGATION SECTION ===
        nav_section = ttk.Frame(main_controls_frame)
        nav_section.pack(side=tk.LEFT, padx=(0, 20), pady=5)
        
        # PDF navigation label (shows when multiple PDFs)
        self.pdf_nav_label = ttk.Label(nav_section, text="", style=self.STYLE_SUBTITLE, foreground='darkblue')
        self.pdf_nav_label.pack(anchor=tk.W)
        
        nav_buttons = ttk.Frame(nav_section)
        nav_buttons.pack()
        
        ttk.Button(nav_buttons, text="⬆️ Prev", command=self.previous_pdf).pack(side=tk.LEFT, padx=(0, 2))
        ttk.Button(nav_buttons, text="⬇️ Next", command=self.next_pdf).pack(side=tk.LEFT)
        
        # === ZOOM SECTION ===
        zoom_section = ttk.Frame(main_controls_frame)
        zoom_section.pack(side=tk.LEFT, padx=(0, 20), pady=5)
        
        ttk.Label(zoom_section, text="Zoom:", style=self.STYLE_SUBTITLE).pack(anchor=tk.W)
        
        zoom_controls = ttk.Frame(zoom_section)
        zoom_controls.pack()
        
        ttk.Button(zoom_controls, text="🔍-", command=self.zoom_out, width=3).pack(side=tk.LEFT, padx=(0, 2))
        
        self.zoom_var = tk.IntVar(value=self.thumbnail_size)
        zoom_scale = ttk.Scale(zoom_controls, from_=self.min_zoom, to=self.max_zoom, 
                              variable=self.zoom_var, orient=tk.HORIZONTAL,
                              command=self.on_zoom_change, length=100)
        zoom_scale.pack(side=tk.LEFT, padx=(2, 2))
        
        ttk.Button(zoom_controls, text="🔍+", command=self.zoom_in, width=3).pack(side=tk.LEFT, padx=(2, 2))
        
        self.zoom_label = ttk.Label(zoom_controls, text=f"{self.thumbnail_size}px", 
                                   style=self.STYLE_SUBTITLE)
        self.zoom_label.pack(side=tk.LEFT, padx=(5, 0))
        
        # === SECOND ROW CONTAINER ===
        second_row = ttk.Frame(control_frame)
        second_row.pack(fill=tk.X, pady=(10, 0))
        
        # === CROP SECTION ===
        crop_section = ttk.Frame(second_row)
        crop_section.pack(side=tk.LEFT, padx=(0, 20), pady=5)
        
        self.crop_mode_var = tk.BooleanVar()
        self.crop_toggle_btn = ttk.Checkbutton(crop_section, text="✂️ Crop Mode", 
                                              variable=self.crop_mode_var,
                                              command=self.toggle_crop_mode)
        self.crop_toggle_btn.pack(anchor=tk.W)
        
        crop_buttons = ttk.Frame(crop_section)
        crop_buttons.pack()
        
        ttk.Button(crop_buttons, text="📄 Extract PDF", command=self.extract_crops_pdf).pack(side=tk.LEFT, padx=(0, 2))
        ttk.Button(crop_buttons, text="🖼️ Extract PNG", command=self.extract_crops_png).pack(side=tk.LEFT)
        
        # === NEW: EDIT SECTION ===
        edit_section = ttk.Frame(second_row)
        edit_section.pack(side=tk.LEFT, padx=(0, 20), pady=5)
        
        self.edit_mode_var = tk.BooleanVar()
        self.edit_toggle_btn = ttk.Checkbutton(edit_section, text="✏️ Edit Mode", 
                                              variable=self.edit_mode_var,
                                              command=self.toggle_edit_mode)
        self.edit_toggle_btn.pack(anchor=tk.W)
        
        edit_buttons = ttk.Frame(edit_section)
        edit_buttons.pack()
        
        ttk.Button(edit_buttons, text="🔄 Reset", command=self.reset_edit_session).pack(side=tk.LEFT, padx=(0, 2))
        ttk.Button(edit_buttons, text="💾 Save PDF", command=self.save_edited_pdf, style='Edit.TButton').pack(side=tk.LEFT)
        
        # Bulk delete section - only visible in edit mode
        self.bulk_delete_frame = ttk.Frame(edit_section)
        
        bulk_delete_label = ttk.Label(self.bulk_delete_frame, text="Delete Current Positions:")
        bulk_delete_label.pack(anchor=tk.W)
        
        # Input frame for entry and button
        bulk_input_frame = ttk.Frame(self.bulk_delete_frame)
        bulk_input_frame.pack(fill=tk.X, pady=(2, 0))
        
        self.bulk_delete_entry = ttk.Entry(bulk_input_frame, width=20,
                                         font=(self.FONT_FAMILY, 9))
        self.bulk_delete_entry.pack(side=tk.LEFT, padx=(0, 5))
        
        # Configure entry field to be properly focusable
        self.bulk_delete_entry.configure(state='normal')
        
        # Bind Enter key to trigger bulk delete
        self.bulk_delete_entry.bind('<Return>', lambda e: self.bulk_delete_pages())
        
        # Ensure entry field can receive focus when clicked
        def focus_entry(event):
            self.bulk_delete_entry.focus_set()
            self.bulk_delete_entry.icursor(tk.END)
            return 'break'  # Prevent event propagation
            
        self.bulk_delete_entry.bind('<Button-1>', focus_entry)
        
        # Also bind to the label click to focus the entry
        bulk_delete_label.bind('<Button-1>', lambda e: self.bulk_delete_entry.focus_set())
        
        ttk.Button(bulk_input_frame, text="❌ Delete", 
                  command=self.bulk_delete_pages).pack(side=tk.LEFT)
        
        # Help text
        help_text = ttk.Label(self.bulk_delete_frame, 
                             text="Enter positions: 1,3,5 or 2-4,7-9 or -5 (pages 1-5) or 3- (page 3 onwards)",
                             font=(self.FONT_FAMILY, 8),
                             foreground='gray')
        help_text.pack(anchor=tk.W)
        
        # Initially hide bulk delete frame
        self.bulk_delete_frame.pack_forget()
        
        # === PRIMARY ACTION (flexible positioning) ===
        primary_section = ttk.Frame(second_row)
        primary_section.pack(side=tk.LEFT, pady=5)
        
        ttk.Label(primary_section, text="Export:", style=self.STYLE_SUBTITLE).pack(anchor=tk.W)
        
        ttk.Button(primary_section, text="📦 Split & Save ZIP", 
                  command=self.split_and_save, style=self.STYLE_ACCENT_BUTTON).pack()
        
        # === FILE INFO (spans across bottom) ===
        info_section = ttk.Frame(control_frame)
        info_section.pack(fill=tk.X, pady=(15, 0))
        
        self.file_label = ttk.Label(info_section, text="No file selected", 
                                   foreground='gray', style=self.STYLE_SUBTITLE)
        self.file_label.pack(anchor=tk.W)
        
        # Edit status label
        self.edit_status_label = ttk.Label(info_section, text="", 
                                          foreground='darkblue', style=self.STYLE_SUBTITLE)
        self.edit_status_label.pack(anchor=tk.W)
        
    def create_content_area(self, parent):
        """Create main content area"""
        paned_window = ttk.PanedWindow(parent, orient=tk.HORIZONTAL)
        paned_window.grid(row=2, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        # PDF preview area (left side)
        preview_frame = ttk.LabelFrame(paned_window, text="📖 PDF Pages", padding="5")
        paned_window.add(preview_frame, weight=2)
        
        # Create scrollable canvas for thumbnails
        canvas_frame = ttk.Frame(preview_frame)
        canvas_frame.pack(fill=tk.BOTH, expand=True)
        canvas_frame.columnconfigure(0, weight=1)
        canvas_frame.rowconfigure(0, weight=1)
        
        self.canvas = tk.Canvas(canvas_frame, bg='white', highlightthickness=0)
        scrollbar_v = ttk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=self.canvas.yview)
        scrollbar_h = ttk.Scrollbar(canvas_frame, orient=tk.HORIZONTAL, command=self.canvas.xview)
        
        self.canvas.configure(yscrollcommand=scrollbar_v.set, xscrollcommand=scrollbar_h.set)
        
        # Grid the canvas and scrollbars
        self.canvas.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        scrollbar_v.grid(row=0, column=1, sticky=(tk.N, tk.S))
        scrollbar_h.grid(row=1, column=0, sticky=(tk.W, tk.E))
        
        # Frame for thumbnails inside canvas
        self.thumbnails_frame = tk.Frame(self.canvas, bg='white')
        self.canvas_window = self.canvas.create_window((0, 0), window=self.thumbnails_frame, anchor=tk.NW)
        
        # Right side - now with two sections
        right_paned = ttk.PanedWindow(paned_window, orient=tk.VERTICAL)
        paned_window.add(right_paned, weight=1)
        
        # Selection panel (top right)
        selection_frame = ttk.LabelFrame(right_paned, text="📋 Selected Ranges", padding="10")
        right_paned.add(selection_frame, weight=1)
        
        # Selected ranges list (give it specific space, not expand=True)
        list_frame = ttk.Frame(selection_frame)
        list_frame.pack(fill=tk.BOTH, expand=False, pady=(0, 10))
        list_frame.columnconfigure(0, weight=1)
        list_frame.rowconfigure(0, weight=1)
        
        columns = ('delete', 'range', 'pages', 'file')
        self.ranges_tree = ttk.Treeview(list_frame, columns=columns, show='headings', height=8)
        
        self.ranges_tree.heading('delete', text='')
        self.ranges_tree.heading('range', text='Page Range')
        self.ranges_tree.heading('pages', text='Pages')
        self.ranges_tree.heading('file', text='PDF File')
        
        self.ranges_tree.column('delete', width=30, anchor=tk.CENTER, minwidth=30)
        self.ranges_tree.column('range', width=120, anchor=tk.CENTER)
        self.ranges_tree.column('pages', width=60, anchor=tk.CENTER)
        self.ranges_tree.column('file', width=150, anchor=tk.W)
        
        # Bind click event for delete column
        self.ranges_tree.bind(self.EVENT_BUTTON_1, self.on_range_tree_click)
        
        # Scrollbar for ranges list
        ranges_scroll = ttk.Scrollbar(list_frame, orient=tk.VERTICAL, command=self.ranges_tree.yview)
        self.ranges_tree.configure(yscrollcommand=ranges_scroll.set)
        
        self.ranges_tree.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        ranges_scroll.grid(row=0, column=1, sticky=(tk.N, tk.S))
        
        # Range controls - should now be visible
        range_controls = ttk.Frame(selection_frame)
        range_controls.pack(fill=tk.X, pady=(0, 5))
        
        # Left side - clear button
        ttk.Button(range_controls, text="🗑️ Clear Ranges", 
                  command=self.clear_ranges_only).pack(side=tk.LEFT)
        
        # Right side - range count label
        self.range_count_var = tk.StringVar(value="0 ranges selected")
        count_label = ttk.Label(range_controls, textvariable=self.range_count_var,
                               style=self.STYLE_SUBTITLE, foreground='darkgreen')
        count_label.pack(side=tk.RIGHT)
        
        # NEW: Crop Preview Panel (bottom right)
        crop_preview_frame = ttk.LabelFrame(right_paned, text="✂️ Crop Previews", padding="10")
        right_paned.add(crop_preview_frame, weight=1)
        
        # Crop preview header
        crop_header_frame = ttk.Frame(crop_preview_frame)
        crop_header_frame.pack(fill=tk.X, pady=(0, 10))
        
        self.crop_count_var = tk.StringVar(value="0 crops")
        crop_count_label = ttk.Label(crop_header_frame, textvariable=self.crop_count_var,
                                    style=self.STYLE_SUBTITLE, foreground='darkred')
        crop_count_label.pack(side=tk.LEFT)
        
        ttk.Button(crop_header_frame, text="🗑️ Clear Crops", 
                  command=self.clear_all_crops).pack(side=tk.RIGHT)
        
        # Scrollable crop preview area (increased height)
        crop_canvas_frame = ttk.Frame(crop_preview_frame)
        crop_canvas_frame.pack(fill=tk.BOTH, expand=True)
        crop_canvas_frame.columnconfigure(0, weight=1)
        crop_canvas_frame.rowconfigure(0, weight=1)
        
        self.crop_canvas = tk.Canvas(crop_canvas_frame, bg='white', highlightthickness=0, height=300)
        crop_scrollbar_v = ttk.Scrollbar(crop_canvas_frame, orient=tk.VERTICAL, command=self.crop_canvas.yview)
        
        self.crop_canvas.configure(yscrollcommand=crop_scrollbar_v.set)
        
        self.crop_canvas.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        crop_scrollbar_v.grid(row=0, column=1, sticky=(tk.N, tk.S))
        
        # Frame for crop thumbnails inside canvas
        self.crop_thumbnails_frame = tk.Frame(self.crop_canvas, bg='white')
        self.crop_canvas_window = self.crop_canvas.create_window((0, 0), window=self.crop_thumbnails_frame, anchor=tk.NW)
        
        # Bind canvas events
        self.canvas.bind(self.EVENT_CONFIGURE, self.on_canvas_configure)
        self.thumbnails_frame.bind(self.EVENT_CONFIGURE, self.on_frame_configure)
        self.crop_canvas.bind(self.EVENT_CONFIGURE, self.on_crop_canvas_configure)
        self.crop_thumbnails_frame.bind(self.EVENT_CONFIGURE, self.on_crop_frame_configure)
        
        # Mouse wheel scrolling with enhanced sensitivity - bind to multiple elements
        # for better coverage
        scroll_widgets = [self.canvas, canvas_frame, preview_frame, self.thumbnails_frame]
        for widget in scroll_widgets:
            widget.bind(self.EVENT_MOUSE_WHEEL, self.on_mousewheel)
            widget.bind(self.EVENT_BUTTON_4, self.on_mousewheel)  # Linux
            widget.bind(self.EVENT_BUTTON_5, self.on_mousewheel)  # Linux
        
        # Mouse wheel for crop canvas
        crop_scroll_widgets = [self.crop_canvas, crop_canvas_frame, self.crop_thumbnails_frame]
        for widget in crop_scroll_widgets:
            widget.bind(self.EVENT_MOUSE_WHEEL, self.on_crop_mousewheel)
            widget.bind(self.EVENT_BUTTON_4, self.on_crop_mousewheel)  # Linux
            widget.bind(self.EVENT_BUTTON_5, self.on_crop_mousewheel)  # Linux
        
        # Keyboard navigation
        self.canvas.bind('<Page_Up>', lambda e: self.canvas.yview_scroll(-10, "units"))
        self.canvas.bind('<Page_Down>', lambda e: self.canvas.yview_scroll(10, "units"))
        self.canvas.bind('<Home>', lambda e: self.canvas.yview_moveto(0))
        self.canvas.bind('<End>', lambda e: self.canvas.yview_moveto(1))
        
        # Ensure canvas clicks don't steal focus from entry fields
        self.canvas.bind('<Button-1>', self.handle_canvas_click)
        
        # Make canvas focusable for keyboard events
        self.canvas.focus_set()

    def handle_canvas_click(self, event):
        """Handle canvas clicks without stealing focus from entry fields"""
        # Check if focus is currently on an entry widget
        focused_widget = self.root.focus_get()
        if focused_widget and isinstance(focused_widget, (ttk.Entry, tk.Entry)):
            # Don't steal focus if an entry field is currently focused
            return
        
        # Otherwise, set focus to root for keyboard navigation
        self.root.focus_set()

    # ===== PAGE EDITING FUNCTIONALITY (REORDER + DELETE + ROTATE) =====
    
    def initialize_edit_session(self):
        """Initialize edit session tracking"""
        if self.pdf_document:
            self.page_order = list(range(len(self.pdf_document)))
            self.original_order = self.page_order.copy()
            self.deleted_pages = set()
            self.original_rotations = getattr(self, 'page_rotations', {}).copy()
            self.has_edited = False
            self.update_edit_status()
    
    def toggle_edit_mode(self):
        """Toggle page edit mode (reorder + delete + rotate)"""
        desired_mode = self.edit_mode_var.get()
        
        # If leaving edit mode and there are changes, prompt user
        if self.edit_mode and not desired_mode:
            if self.has_edited or self.deleted_pages or self.page_rotations:
                choice = self.prompt_edit_exit()
                if choice == "cancel":
                    # User cancelled, revert checkbox
                    self.edit_mode_var.set(True)
                    return
                elif choice == "discard":
                    self.discard_edit_changes()
                elif choice == "update":
                    self.apply_edit_changes_to_pdf()
        
        self.edit_mode = desired_mode
        
        if self.edit_mode:
            # Disable crop mode when entering edit mode
            if self.crop_mode:
                self.crop_mode_var.set(False)
                self.toggle_crop_mode()
            
            self.status_var.set("Edit mode enabled - Drag to reorder • Click X to delete • Rotate pages")
            # Change background color to indicate edit mode
            self.thumbnails_frame.config(bg=self.colors['edit_mode'])
            
            # Show bulk delete frame
            if hasattr(self, 'bulk_delete_frame'):
                self.bulk_delete_frame.pack(pady=(10, 0))
            
            # Show edit instructions
            self.show_edit_instructions()
        else:
            self.status_var.set("Page selection mode enabled")
            self.thumbnails_frame.config(bg='white')
            
            # Hide bulk delete frame
            if hasattr(self, 'bulk_delete_frame'):
                self.bulk_delete_frame.pack_forget()
            
        # Update display to reflect mode change without rebuilding thumbnails
        if self.page_thumbnails:
            # Just refresh the display layout, don't rebuild thumbnails
            self.display_thumbnails(force_rebuild=True)
    
    def prompt_edit_exit(self):
        """Prompt user when exiting edit mode with unsaved changes"""
        # Create a custom dialog with three buttons
        dialog = tk.Toplevel(self.root)
        dialog.title("Exit Edit Mode")
        dialog.geometry("400x200")
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Center the dialog
        dialog.geometry("+%d+%d" % (self.root.winfo_rootx() + 50, self.root.winfo_rooty() + 50))
        
        result = {"choice": "cancel"}
        
        # Main message
        message_frame = ttk.Frame(dialog)
        message_frame.pack(pady=20, padx=20, fill=tk.BOTH, expand=True)
        
        ttk.Label(message_frame, text="You have unsaved changes in edit mode.", 
                 font=(self.FONT_FAMILY, 12, 'bold')).pack(pady=(0, 10))
        
        ttk.Label(message_frame, text="What would you like to do?", 
                 font=(self.FONT_FAMILY, 10)).pack(pady=(0, 20))
        
        # Buttons frame
        buttons_frame = ttk.Frame(message_frame)
        buttons_frame.pack(pady=10)
        
        def on_discard():
            result["choice"] = "discard"
            dialog.destroy()
            
        def on_update():
            result["choice"] = "update"
            dialog.destroy()
            
        def on_cancel():
            result["choice"] = "cancel"
            dialog.destroy()
        
        ttk.Button(buttons_frame, text="🗑️ Discard Changes", 
                  command=on_discard).pack(side=tk.LEFT, padx=5)
        ttk.Button(buttons_frame, text="💾 Update PDF", 
                  command=on_update).pack(side=tk.LEFT, padx=5)
        ttk.Button(buttons_frame, text="❌ Cancel", 
                  command=on_cancel).pack(side=tk.LEFT, padx=5)
        
        # Bind Escape to cancel
        dialog.bind('<Escape>', lambda e: on_cancel())
        
        # Wait for dialog to close
        dialog.wait_window()
        
        return result["choice"]
    
    def discard_edit_changes(self):
        """Discard all edit changes and restore original state"""
        try:
            # Restore original order
            self.page_order = self.original_order.copy()
            self.has_edited = False
            
            # Clear deleted pages
            self.deleted_pages.clear()
            
            # Restore original rotations
            self.page_rotations = self.original_rotations.copy()
            
            # Regenerate thumbnails with original rotations if needed
            if self.original_rotations != self.page_rotations:
                threading.Thread(target=self.generate_thumbnails, daemon=True).start()
            else:
                # Just refresh display
                self.display_thumbnails(force_rebuild=True)
            
            self.update_edit_status()
            self.update_file_label()
            self.status_var.set("Edit changes discarded - PDF restored to original state")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to discard changes: {str(e)}")
    
    def apply_edit_changes_to_pdf(self):
        """Apply edit changes permanently to the loaded PDF document"""
        try:
            if not self.has_edited and not self.deleted_pages and not self.page_rotations:
                self.status_var.set("No changes to apply")
                return
            
            self.status_var.set("Applying changes to PDF...")
            self.root.update()
            
            # Create a new PDF document with the changes applied
            import tempfile
            temp_path = tempfile.mktemp(suffix=".pdf")
            
            # Create new document using PyPDF2 to apply changes
            from PyPDF2 import PdfWriter, PdfReader
            
            # First, save the current PDF document (which might be already modified) to a temp file
            current_temp_path = tempfile.mktemp(suffix="_current.pdf")
            self.pdf_document.save(current_temp_path)
            
            # Read from the current PDF (original or previously modified)
            with open(current_temp_path, 'rb') as file:
                pdf_reader = PdfReader(file)
                pdf_writer = PdfWriter()
                
                # Add pages in the new order, skipping deleted pages, with rotations
                for page_index in self.page_order:
                    if page_index in self.deleted_pages:
                        continue
                    
                    page = pdf_reader.pages[page_index]
                    
                    # Apply rotation if set for this page (1-based page number)
                    page_number = page_index + 1
                    if page_number in self.page_rotations:
                        rotation_angle = self.page_rotations[page_number]
                        page.rotate(rotation_angle)
                    
                    pdf_writer.add_page(page)
                
                # Write to final temporary file
                with open(temp_path, 'wb') as output_file:
                    pdf_writer.write(output_file)
            
            # Clean up the temporary current file
            try:
                os.remove(current_temp_path)
            except:
                pass
            
            # Track modification for this specific PDF
            current_pdf_path = self.pdf_path
            self.pdf_modifications[current_pdf_path] = {
                'temp_path': temp_path,
                'original_path': current_pdf_path
            }
            
            # Close the current PDF document
            if self.pdf_document:
                self.pdf_document.close()
            
            # Load the modified PDF document
            self.pdf_document = fitz.open(temp_path)
            
            # Update the cache with the new document, keeping the original path as key
            # This ensures folder navigation continues to work properly
            self.pdf_documents[current_pdf_path] = self.pdf_document
            
            # Reset edit state since changes are now applied
            self.initialize_edit_session()
            
            # Regenerate thumbnails for the modified PDF
            threading.Thread(target=self.generate_thumbnails, daemon=True).start()
            
            # Update file label to show modified state
            self.update_file_label()
            self.status_var.set("Changes applied successfully - PDF updated for this session")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to apply changes to PDF: {str(e)}")
            self.status_var.set("Error applying changes")
    
    def update_file_label(self):
        """Update file label to show current state and modifications"""
        if not self.pdf_document:
            return
            
        filename = os.path.basename(self.pdf_path) if self.pdf_path else "Unknown"
        page_count = len(self.pdf_document)
        
        # Show different states based on PDF origin
        if self.pdf_path in self.pdf_modifications:
            # PDF has been modified during this session
            text = f"{filename} (Modified - {page_count} pages)"
            color = 'darkblue'
        elif self.is_merged_pdf:
            # Merged PDF
            text = f"Merged PDF - {page_count} pages"
            color = 'darkgreen'
        else:
            # Original unmodified PDF
            text = f"{filename} ({page_count} pages)"
            color = 'black'
            
        self.file_label.config(text=text, foreground=color)
    
    def get_actual_pdf_path(self, original_path):
        """Get the actual PDF path to use (modified temp file if exists, otherwise original)"""
        if original_path in self.pdf_modifications:
            return self.pdf_modifications[original_path]['temp_path']
        return original_path
    
    def show_edit_instructions(self):
        """Show brief instructions for edit mode"""
        # Show as temporary status message
        self.edit_status_label.config(text="Drag to reorder • Click ❌ to delete • Rotate with ↺↻ • Blue zones show drop locations")
    
    def setup_drag_and_drop(self, widget, page_index):
        """Setup drag and drop bindings for a page widget"""
        if not self.edit_mode:
            return
            
        # Get the main frame for the page
        frame = widget['frame']
        
        # Bind drag events to the main frame and its children (but not delete button)
        drag_widgets = [frame, widget['page_label'], widget['thumb_label']]
        
        for drag_widget in drag_widgets:
            drag_widget.bind(self.EVENT_BUTTON_1, lambda e, idx=page_index: self.start_drag(e, idx))
            drag_widget.bind('<B1-Motion>', lambda e, idx=page_index: self.on_drag(e, idx))
            drag_widget.bind('<ButtonRelease-1>', lambda e, idx=page_index: self.end_drag(e, idx))
    
    def delete_page(self, page_index):
        """Delete a page from the current edit session"""
        if not self.edit_mode:
            return
            
        # Get the actual page number being deleted
        actual_page_index = self.page_order[page_index]
        page_number = actual_page_index + 1
        
        if messagebox.askyesno("Delete Page", f"Delete page {page_number} from the current edit session?\n\nThis can be undone with 'Reset'."):
            # Add to deleted pages set
            self.deleted_pages.add(actual_page_index)
            
            # Remove from current page order
            self.page_order.pop(page_index)
            
            # Mark as edited
            self.has_edited = True
            
            # Update display
            self.regenerate_ordered_thumbnails()
            self.update_edit_status()
            
            # Update status
            remaining_pages = len(self.page_order)
            self.status_var.set(f"Deleted page {page_number}. {remaining_pages} pages remaining.")
    
    def parse_page_ranges(self, range_string):
        """Parse page range string into list of page numbers"""
        if not range_string.strip():
            return []
            
        pages = set()
        try:
            # Get current visible page count for range validation
            current_visible_pages = [idx for idx in self.page_order if idx not in self.deleted_pages]
            current_page_count = len(current_visible_pages)
            
            # Split by commas and process each part
            parts = [part.strip() for part in range_string.split(',')]
            
            for part in parts:
                if part.startswith('-') and len(part) > 1:
                    # Handle "-[page]" syntax - delete all pages from 1 to page (inclusive)
                    end_page = int(part[1:].strip())
                    if end_page < 1:
                        raise ValueError(f"Page number must be positive: {part}")
                    if end_page > current_page_count:
                        raise ValueError(f"Page {end_page} exceeds current page count ({current_page_count})")
                    pages.update(range(1, end_page + 1))
                elif part.endswith('-') and len(part) > 1:
                    # Handle "[page]-" syntax - delete all pages from page to end (inclusive)
                    start_page = int(part[:-1].strip())
                    if start_page < 1:
                        raise ValueError(f"Page number must be positive: {part}")
                    if start_page > current_page_count:
                        raise ValueError(f"Page {start_page} exceeds current page count ({current_page_count})")
                    pages.update(range(start_page, current_page_count + 1))
                elif '-' in part and not part.startswith('-') and not part.endswith('-'):
                    # Handle standard ranges like "2-5"
                    start, end = part.split('-', 1)
                    start = int(start.strip())
                    end = int(end.strip())
                    
                    if start > end:
                        start, end = end, start  # Swap if reversed
                        
                    pages.update(range(start, end + 1))
                elif part == '-':
                    # Handle standalone "-" as invalid
                    raise ValueError("Invalid format: standalone '-' is not allowed")
                else:
                    # Handle single pages
                    page_num = int(part.strip())
                    pages.add(page_num)
                    
            return sorted(list(pages))
            
        except ValueError as e:
            if "invalid literal for int()" in str(e):
                raise ValueError("Invalid format. Use numbers and ranges like: 1,3,5-7,10, or use -5 (pages 1-5) or 3- (page 3 onwards)")
            else:
                raise e
    
    def bulk_delete_pages(self):
        """Delete multiple pages based on user input (using current display positions)"""
        if not self.edit_mode:
            return
            
        if not self.pdf_document:
            messagebox.showwarning("Warning", "Please load a PDF file first.")
            return
            
        range_text = self.bulk_delete_entry.get().strip()
        if not range_text:
            messagebox.showwarning("Warning", "Please enter page positions to delete.")
            return
        
        try:
            # Parse the input as display positions
            positions_to_delete = self.parse_page_ranges(range_text)
            
            if not positions_to_delete:
                messagebox.showwarning("Warning", "No valid positions specified.")
                return
            
            # Get current visible pages (excluding already deleted ones)
            current_visible_pages = [idx for idx in self.page_order if idx not in self.deleted_pages]
            current_page_count = len(current_visible_pages)
            
            # Validate positions against current visible page count
            invalid_positions = [p for p in positions_to_delete if p < 1 or p > current_page_count]
            if invalid_positions:
                messagebox.showerror("Error", f"Invalid positions: {', '.join(map(str, invalid_positions))}\nValid range: 1-{current_page_count} (current visible pages)")
                return
            
            # Convert display positions to actual page indices
            actual_page_indices_to_delete = []
            original_page_numbers = []  # For display in confirmation
            
            for position in positions_to_delete:
                # Convert 1-based position to 0-based index in current visible pages
                visible_index = position - 1
                if visible_index < len(current_visible_pages):
                    actual_page_index = current_visible_pages[visible_index]
                    actual_page_indices_to_delete.append(actual_page_index)
                    original_page_numbers.append(actual_page_index + 1)  # For display (original page number)
            
            if not actual_page_indices_to_delete:
                messagebox.showwarning("Warning", "No valid pages to delete.")
                return
            
            # Show confirmation with both current positions and original page numbers
            positions_str = ', '.join(map(str, positions_to_delete))
            original_pages_str = ', '.join(map(str, original_page_numbers))
            
            if len(positions_to_delete) == 1:
                message = f"Delete current position {positions_str} (original page {original_pages_str})?"
            else:
                message = f"Delete {len(positions_to_delete)} pages at positions {positions_str}?\n(Original pages: {original_pages_str})\n\nThis can be undone with 'Reset'."
            
            if messagebox.askyesno("Bulk Delete Pages", message):
                # Add pages to deleted set
                self.deleted_pages.update(actual_page_indices_to_delete)
                
                # Remove from current page order
                self.page_order = [p for p in self.page_order if p not in actual_page_indices_to_delete]
                
                # Mark as edited
                self.has_edited = True
                
                # Clear the input field
                self.bulk_delete_entry.delete(0, tk.END)
                
                # Update display
                self.regenerate_ordered_thumbnails()
                self.update_edit_status()
                
                # Update status
                remaining_pages = len(self.page_order)
                deleted_count = len(positions_to_delete)
                self.status_var.set(f"Deleted {deleted_count} page{'s' if deleted_count > 1 else ''}. {remaining_pages} pages remaining.")
                
        except ValueError as e:
            messagebox.showerror("Error", str(e))
        except Exception as e:
            messagebox.showerror("Error", f"Failed to delete pages: {str(e)}")
    
    def start_drag(self, event, page_index):
        """Start dragging a page"""
        if not self.edit_mode:
            return
            
        # Store drag information
        self.drag_data = {
            'source_index': page_index,
            'source_page_num': self.page_order[page_index],
            'start_x': event.x_root,
            'start_y': event.y_root,
            'has_moved': False
        }
        
        # Visual feedback - highlight source page
        source_widget = self.page_widgets[page_index]
        if source_widget:
            self.set_page_color(source_widget, self.colors['drag_source'])
            source_widget['frame'].config(relief=tk.SOLID, borderwidth=3)
        
        # Change cursor
        self.root.config(cursor="hand2")
    
    def on_drag(self, event, page_index):
        """Handle page dragging"""
        if not self.edit_mode or not self.drag_data:
            return
            
        # Mark that we've started moving
        if not self.drag_data['has_moved']:
            # Check if we've moved enough to start drag
            dx = abs(event.x_root - self.drag_data['start_x'])
            dy = abs(event.y_root - self.drag_data['start_y'])
            if dx > 10 or dy > 10:
                self.drag_data['has_moved'] = True
                self.create_drag_ghost(event)
        
        if self.drag_data['has_moved']:
            # Update ghost position
            self.update_drag_ghost(event)
            
            # Highlight drop zones
            self.highlight_drop_zones(event)
    
    def create_drag_ghost(self, event):
        """Create a ghost image while dragging"""
        try:
            # Create a semi-transparent window following the cursor
            self.drag_ghost = tk.Toplevel(self.root)
            self.drag_ghost.wm_overrideredirect(True)
            self.drag_ghost.attributes('-alpha', 0.7)
            self.drag_ghost.attributes('-topmost', True)
            
            # Get the thumbnail image
            source_index = self.drag_data['source_index']
            source_widget = self.page_widgets[source_index]
            
            if source_widget and 'thumb_label' in source_widget:
                # Create a label with the thumbnail
                ghost_label = tk.Label(self.drag_ghost, 
                                     image=source_widget['thumb_label']['image'],
                                     text=f"Page {self.drag_data['source_page_num'] + 1}",
                                     compound=tk.TOP,
                                     font=(self.FONT_FAMILY, 10, 'bold'),
                                     bg=self.colors['drag_source'],
                                     relief=tk.SOLID,
                                     borderwidth=2)
                ghost_label.pack()
            
            # Position the ghost
            self.update_drag_ghost(event)
            
        except Exception as e:
            pass
    
    def update_drag_ghost(self, event):
        """Update ghost position"""
        if self.drag_ghost:
            # Position slightly offset from cursor
            x = event.x_root + 10
            y = event.y_root + 10
            self.drag_ghost.geometry(f"+{x}+{y}")
    
    def highlight_drop_zones(self, event):
        """Highlight valid drop zones during drag"""
        # Clear previous highlights
        self.clear_drop_highlights()
        
        # Find the drop target
        target_index = self.find_drop_target(event)
        
        if target_index is not None and target_index != self.drag_data['source_index']:
            # Highlight drop zone
            self.show_drop_indicator(target_index)
    
    def find_drop_target(self, event):
        """Find which page index the cursor is over"""
        try:
            # Convert screen coordinates to canvas coordinates
            canvas_x = self.canvas.canvasx(event.x_root - self.canvas.winfo_rootx())
            canvas_y = self.canvas.canvasy(event.y_root - self.canvas.winfo_rooty())
            
            # Find the widget under the cursor
            for i, widget in enumerate(self.page_widgets):
                if widget is None:
                    continue
                    
                frame = widget['frame']
                
                # Get frame position relative to canvas
                frame_x = frame.winfo_x()
                frame_y = frame.winfo_y()
                frame_width = frame.winfo_width()
                frame_height = frame.winfo_height()
                
                # Check if cursor is over this frame
                if (frame_x <= canvas_x <= frame_x + frame_width and
                    frame_y <= canvas_y <= frame_y + frame_height):
                    return i
            
            return None
            
        except Exception as e:
            pass
            return None
    
    def show_drop_indicator(self, target_index):
        """Show visual indicator for drop target"""
        if target_index < len(self.page_widgets) and self.page_widgets[target_index]:
            target_widget = self.page_widgets[target_index]
            
            # Highlight the target page
            self.set_page_color(target_widget, self.colors['drop_zone'])
            target_widget['frame'].config(relief=tk.RIDGE, borderwidth=3)
    
    def clear_drop_highlights(self):
        """Clear all drop zone highlights"""
        for i, widget in enumerate(self.page_widgets):
            if widget is None:
                continue
                
            # Skip the source page (keep it highlighted)
            if (self.drag_data and i == self.drag_data['source_index']):
                continue
                
            # Reset to normal appearance
            if not self.is_page_selected(self.page_order[i] + 1):  # Convert to 1-based page number
                self.set_page_color(widget, self.colors['edit_mode'] if self.edit_mode else self.colors['normal'])
                widget['frame'].config(relief=tk.RAISED, borderwidth=2)
    
    def end_drag(self, event, page_index):
        """End page dragging"""
        if not self.edit_mode or not self.drag_data:
            return
            
        try:
            # Clean up visual elements
            if self.drag_ghost:
                self.drag_ghost.destroy()
                self.drag_ghost = None
            
            self.root.config(cursor="")
            self.clear_drop_highlights()
            
            # If we actually dragged (not just a click)
            if self.drag_data.get('has_moved', False):
                target_index = self.find_drop_target(event)
                
                if target_index is not None and target_index != self.drag_data['source_index']:
                    # Perform the reorder
                    self.reorder_pages(self.drag_data['source_index'], target_index)
            
            # Reset source page appearance
            source_widget = self.page_widgets[self.drag_data['source_index']]
            if source_widget:
                if not self.is_page_selected(self.drag_data['source_page_num'] + 1):
                    self.set_page_color(source_widget, self.colors['edit_mode'] if self.edit_mode else self.colors['normal'])
                source_widget['frame'].config(relief=tk.RAISED, borderwidth=2)
            
        except Exception as e:
            pass
        finally:
            # Clear drag data
            self.drag_data = None
    
    def reorder_pages(self, source_index, target_index):
        """Reorder pages by moving source to target position"""
        if source_index == target_index:
            return
            
        try:
            # Get the page number being moved
            page_num = self.page_order[source_index]
            
            # Remove from source position
            self.page_order.pop(source_index)
            
            # Adjust target index if necessary
            if target_index > source_index:
                target_index -= 1
            
            # Insert at target position
            self.page_order.insert(target_index, page_num)
            
            # Mark as edited
            self.has_edited = True
            
            # Update display
            self.regenerate_ordered_thumbnails()
            self.update_edit_status()
            
            # Update status
            self.status_var.set(f"Moved page {page_num + 1} to position {target_index + 1}")
            
        except Exception as e:
            pass
            messagebox.showerror("Reorder Error", f"Failed to reorder pages: {str(e)}")
    
    def regenerate_ordered_thumbnails(self):
        """Refresh the thumbnail display after reorder/delete operations"""
        if not self.pdf_document or not self.page_order:
            return
            
        try:
            # Just refresh the display - thumbnails stay indexed by original page numbers
            # The display logic in display_thumbnails() now handles the correct ordering
            self.display_thumbnails(force_rebuild=True)
            
            # Update edit status
            self.update_edit_status()
            
        except Exception as e:
            pass
            # Simple fallback: just try to display what we have
            self.display_thumbnails(force_rebuild=True)
    
    def reset_edit_session(self):
        """Reset pages to original order, restore deleted pages, and reset rotations"""
        if not self.has_edited and not self.deleted_pages and not self.page_rotations:
            messagebox.showinfo("Info", "No edits to reset - pages are in original state.")
            return
            
        changes = []
        if self.has_edited:
            changes.append("page order")
        if self.deleted_pages:
            changes.append(f"{len(self.deleted_pages)} deleted pages")
        if self.page_rotations:
            changes.append(f"{len(self.page_rotations)} rotated pages")
            
        change_text = ", ".join(changes)
        
        if messagebox.askyesno("Reset Edit Session", f"Reset all changes in this edit session?\n\nThis will restore:\n• {change_text}"):
            try:
                # Reset order
                self.page_order = self.original_order.copy()
                self.has_edited = False
                
                # Restore deleted pages
                self.deleted_pages.clear()
                
                # Reset rotations to original state
                self.page_rotations = self.original_rotations.copy()
                
                # Regenerate thumbnails in original order and state
                self.regenerate_ordered_thumbnails()
                self.update_edit_status()
                
                self.status_var.set("Edit session reset - all changes undone")
                
            except Exception as e:
                messagebox.showerror("Error", f"Failed to reset edit session: {str(e)}")
    
    def update_edit_status(self):
        """Update the edit status display"""
        status_parts = []
        
        if self.has_edited:
            status_parts.append("reordered")
        if self.deleted_pages:
            status_parts.append(f"{len(self.deleted_pages)} deleted")
        if self.page_rotations:
            status_parts.append(f"{len(self.page_rotations)} rotated")
            
        if status_parts:
            total_pages = len(self.page_order)
            status_text = f"📝 Pages edited - {total_pages} pages ({', '.join(status_parts)})"
            self.edit_status_label.config(text=status_text)
        else:
            self.edit_status_label.config(text="")
    
    def save_edited_pdf(self):
        """Save the PDF with current edits (order, deletions, rotations)"""
        if not self.pdf_document:
            messagebox.showwarning("Warning", "Please load a PDF file first.")
            return
            
        if not self.has_edited and not self.deleted_pages and not self.page_rotations:
            messagebox.showinfo("Info", "No edits to save - PDF is in original state.")
            return
            
        # Get filename choice from user
        if self.is_merged_pdf and self.merged_first_pdf_name:
            # For merged PDFs, use first PDF name + merged
            default_name = f"{self.merged_first_pdf_name}_merged.pdf"
        else:
            # For regular PDFs, use original naming
            default_name = Path(self.pdf_path).stem + "_edited.pdf" if self.pdf_path else "edited.pdf"
        
        chosen_filename = self.get_custom_filename(default_name, "PDF")
        if not chosen_filename:
            return
        
        save_path = filedialog.asksaveasfilename(
            title="Save Edited PDF",
            defaultextension=".pdf",
            initialfile=chosen_filename,
            filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")]
        )
        
        if not save_path:
            return
            
        try:
            self.status_var.set("Saving edited PDF...")
            self.root.update()
            
            # Create new PDF with edited pages (only non-deleted pages in current order)
            with open(self.pdf_path, 'rb') as file:
                pdf_reader = PyPDF2.PdfReader(file)
                pdf_writer = PyPDF2.PdfWriter()
                
                # Add pages in the new order, skipping deleted pages
                for page_index in self.page_order:
                    # Skip if this page was deleted
                    if page_index in self.deleted_pages:
                        continue
                        
                    if page_index < len(pdf_reader.pages):
                        page = pdf_reader.pages[page_index]
                        
                        # Apply rotation if set for this page (1-based)
                        page_number_1based = page_index + 1
                        if page_number_1based in self.page_rotations:
                            rotation_angle = self.page_rotations[page_number_1based]
                            if rotation_angle == 90:
                                page = page.rotate(90)
                            elif rotation_angle == 180:
                                page = page.rotate(180)
                            elif rotation_angle == 270:
                                page = page.rotate(270)
                        
                        pdf_writer.add_page(page)
                
                # Write to file
                with open(save_path, 'wb') as output_file:
                    pdf_writer.write(output_file)
            
            # Show success message with details
            saved_pages = len(self.page_order) - len(self.deleted_pages)
            original_pages = len(self.original_order)
            
            details = []
            if self.has_edited:
                details.append("reordered pages")
            if self.deleted_pages:
                details.append(f"removed {len(self.deleted_pages)} pages")
            if self.page_rotations:
                details.append(f"applied {len(self.page_rotations)} rotations")
                
            edit_summary = ", ".join(details) if details else "no changes"
            
            messagebox.showinfo("Success", 
                f"Edited PDF saved successfully!\n\n"
                f"Original: {original_pages} pages\n"
                f"Saved: {saved_pages} pages\n"
                f"Edits: {edit_summary}\n\n"
                f"Saved to:\n{save_path}")
            self.status_var.set("Edited PDF saved successfully!")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to save edited PDF:\n{str(e)}")
            self.status_var.set("Error saving edited PDF")

    def on_crop_canvas_configure(self, event):
        """Handle crop canvas resize"""
        canvas_width = event.width
        self.crop_canvas.itemconfig(self.crop_canvas_window, width=canvas_width)
        
    def on_crop_frame_configure(self, event):
        """Handle crop thumbnails frame resize"""
        self.crop_canvas.configure(scrollregion=self.crop_canvas.bbox("all"))
        
    def on_crop_mousewheel(self, event):
        """Handle mouse wheel scrolling for crop canvas"""
        if event.delta:
            delta = -1 * (event.delta / 120)
        else:
            if event.num == 4:
                delta = -1
            elif event.num == 5:
                delta = 1
            else:
                return
        self.crop_canvas.yview_scroll(int(delta * 3), "units")
        
    def load_pdf_folder(self):
        """Load all PDF files from a selected folder"""
        folder_path = filedialog.askdirectory(
            title="Select Folder Containing PDF Files"
        )
        
        if not folder_path:
            return
            
        try:
            # Find all PDF files in the folder (case-insensitive, no duplicates)
            pdf_files = []
            for filename in os.listdir(folder_path):
                if filename.lower().endswith('.pdf'):
                    pdf_files.append(os.path.join(folder_path, filename))
            
            if not pdf_files:
                messagebox.showwarning("Warning", "No PDF files found in the selected folder.")
                return
            
            # Sort files alphabetically
            pdf_files.sort()
            
            self.status_var.set(f"Loading {len(pdf_files)} PDF files...")
            self.root.update()
            
            # Store PDF list and reset index
            self.pdf_list = pdf_files
            self.current_pdf_index = 0
            self.pdf_documents.clear()  # Clear document cache
            
            # Clear previous selections
            self.clear_selection()
            
            # Update navigation label
            self.update_pdf_navigation_label()
            
            # Load the first PDF
            self.load_current_pdf()
            
            self.status_var.set(f"Loaded folder with {len(pdf_files)} PDF files")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load folder:\n{str(e)}")
            self.status_var.set("Error loading folder")
            
    def load_current_pdf(self):
        """Load the current PDF from the PDF list"""
        if not self.pdf_list or self.current_pdf_index >= len(self.pdf_list):
            return
            
        current_pdf_path = self.pdf_list[self.current_pdf_index]
        
        try:
            # Check if PDF is already cached
            if current_pdf_path not in self.pdf_documents:
                self.pdf_documents[current_pdf_path] = fitz.open(current_pdf_path)
            
            self.pdf_document = self.pdf_documents[current_pdf_path]
            self.pdf_path = current_pdf_path
            
            if len(self.pdf_document) == 0:
                messagebox.showerror("Error", f"PDF '{os.path.basename(current_pdf_path)}' appears to be empty.")
                return
            
            # Reset rotations when loading new PDF
            self.page_rotations = {}
            
            # Reset merge state
            self.is_merged_pdf = False
            self.merged_first_pdf_name = None
            self.update_merge_ui()
            
            # Initialize edit session tracking
            self.initialize_edit_session()
            
            # Update UI
            self.update_file_label()
            
            # Update navigation label
            self.update_pdf_navigation_label()
            
            # Generate thumbnails in background thread
            self.status_var.set("Generating thumbnails...")
            threading.Thread(target=self.generate_thumbnails, daemon=True).start()
            
            # Ensure root window has focus for keyboard events
            self.root.focus_set()
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load PDF '{os.path.basename(current_pdf_path)}':\n{str(e)}")
            
    def update_pdf_navigation_label(self):
        """Update the PDF navigation label"""
        if len(self.pdf_list) <= 1:
            self.pdf_nav_label.config(text="")
        else:
            current = self.current_pdf_index + 1
            total = len(self.pdf_list)
            self.pdf_nav_label.config(text=f"PDF {current} of {total}")
            
    def previous_pdf(self):
        """Navigate to the previous PDF in the list"""
        if len(self.pdf_list) <= 1:
            return
            
        if self.current_pdf_index > 0:
            self.current_pdf_index -= 1
            self.load_current_pdf()
        else:
            # Loop to last PDF
            self.current_pdf_index = len(self.pdf_list) - 1
            self.load_current_pdf()
            
    def next_pdf(self):
        """Navigate to the next PDF in the list"""
        if len(self.pdf_list) <= 1:
            return
            
        if self.current_pdf_index < len(self.pdf_list) - 1:
            self.current_pdf_index += 1
            self.load_current_pdf()
        else:
            # Loop to first PDF
            self.current_pdf_index = 0
            self.load_current_pdf()
            
    def scroll_pages(self, direction):
        """Scroll through pages of current PDF (up/down arrow keys)"""
        if direction < 0:
            # Scroll up (up arrow key)
            self.canvas.yview_scroll(-5, "units")
        else:
            # Scroll down (down arrow key)
            self.canvas.yview_scroll(5, "units")
    
    def on_mousewheel(self, event):
        """Handle mouse wheel scrolling with enhanced sensitivity and Ctrl+wheel zoom"""
        # Check if Ctrl is held down for zooming
        if event.state & 0x4:  # Ctrl key is pressed
            self.handle_zoom_wheel(event)
            return
            
        # Determine scroll direction and amount
        if event.delta:
            # Windows and MacOS
            delta = -1 * (event.delta / 120)
        else:
            # Linux
            if event.num == 4:
                delta = -1
            elif event.num == 5:
                delta = 1
            else:
                return
        
        # Enhanced scrolling - more responsive
        if self.view_mode == 'single':
            # Faster scrolling in single page mode
            scroll_amount = int(delta * 5)
        else:
            # Standard scrolling in grid mode
            scroll_amount = int(delta * 3)
            
        self.canvas.yview_scroll(scroll_amount, "units")
        
    def handle_zoom_wheel(self, event):
        """Handle Ctrl+mouse wheel for zooming (like in web browsers)"""
        # Determine zoom direction
        if event.delta:
            # Windows and MacOS
            zoom_delta = event.delta / 120
        else:
            # Linux
            if event.num == 4:
                zoom_delta = 1  # Zoom in
            elif event.num == 5:
                zoom_delta = -1  # Zoom out
            else:
                return
        
        # Calculate new zoom level
        current_zoom = self.thumbnail_size
        zoom_increment = 25  # Smaller increments for smoother zooming
        
        if zoom_delta > 0:
            # Zoom in
            new_zoom = min(self.max_zoom, current_zoom + zoom_increment)
        else:
            # Zoom out
            new_zoom = max(self.min_zoom, current_zoom - zoom_increment)
        
        # Apply zoom if changed
        if new_zoom != current_zoom:
            self.zoom_var.set(new_zoom)
            self.on_zoom_change(new_zoom)
        
    def load_pdf(self):
        """Load a single PDF file"""
        file_path = filedialog.askopenfilename(
            title="Select PDF File",
            filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")]
        )
        
        if not file_path:
            return
            
        try:
            self.status_var.set("Loading PDF...")
            self.root.update()
            
            # Reset to single PDF mode
            self.pdf_list = [file_path]
            self.current_pdf_index = 0
            self.pdf_documents.clear()
            
            # Load PDF with PyMuPDF
            self.pdf_document = fitz.open(file_path)
            self.pdf_documents[file_path] = self.pdf_document
            
            if len(self.pdf_document) == 0:
                messagebox.showerror("Error", "PDF appears to be empty.")
                return
            
            # Store PDF info
            self.pdf_path = file_path
            filename = os.path.basename(file_path)
            
            # Reset edit session state when loading new PDF (but keep per-PDF modifications)
            # The pdf_modifications dict will persist to track changes across different PDFs
            
            # Reset rotations when loading new PDF
            self.page_rotations = {}
            
            # Reset merge state
            self.is_merged_pdf = False
            self.merged_first_pdf_name = None
            self.update_merge_ui()
            
            # Initialize edit session tracking
            self.initialize_edit_session()
            
            # Update UI
            self.update_file_label()
            self.status_var.set(f"PDF loaded - {len(self.pdf_document)} pages")
            
            # Update navigation (hide for single PDF)
            self.update_pdf_navigation_label()
            
            # Clear previous selection
            self.clear_selection()
            
            # Generate thumbnails in background thread
            self.status_var.set("Generating thumbnails...")
            threading.Thread(target=self.generate_thumbnails, daemon=True).start()
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load PDF:\n{str(e)}")
            self.status_var.set("Error loading PDF")
            
    def generate_thumbnails(self):
        """Generate thumbnail images for all pages"""
        try:
            # Clear thumbnails but preserve order by using a list with proper indexing
            total_pages = len(self.pdf_document)
            self.page_thumbnails = [None] * total_pages  # Pre-allocate list with correct size
            
            
            # Show progress
            self.root.after(0, lambda: self.progress_bar.grid(row=3, column=0, sticky=(tk.W, tk.E), pady=(10, 0)))
            
            # Process pages in order and store at correct index
            for page_num in range(total_pages):
                # Update progress
                progress = (page_num / total_pages) * 100
                self.root.after(0, lambda p=progress: self.progress_var.set(p))
                self.root.after(0, lambda p=page_num+1, t=total_pages: 
                               self.status_var.set(f"Generating thumbnails... {p}/{t}"))
                
                # Render page at current zoom level
                page = self.pdf_document[page_num]
                
                # Calculate zoom factor to fit thumbnail size
                page_rect = page.rect
                zoom = self.thumbnail_size / max(page_rect.width, page_rect.height)
                mat = fitz.Matrix(zoom, zoom)
                
                # Apply rotation if set for this page
                page_number = page_num + 1
                if page_number in self.page_rotations:
                    rotation_angle = self.page_rotations[page_number]
                    mat = mat * fitz.Matrix(rotation_angle)
                
                # Render page
                pix = page.get_pixmap(matrix=mat)
                img_data = pix.tobytes("ppm")
                
                # Create PIL image and convert to PhotoImage
                img = Image.open(io.BytesIO(img_data))
                photo = ImageTk.PhotoImage(img)
                
                # Store at correct index to maintain order
                self.page_thumbnails[page_num] = photo
                
            # Verify thumbnails were created (allow some failures)
            failed_count = self.page_thumbnails.count(None)
            if failed_count > 0:
                pass
                
            # Update UI on main thread
            self.root.after(0, lambda: self.display_thumbnails(force_rebuild=True))
            self.root.after(0, lambda: self.progress_bar.grid_remove())
            
            # Set status based on success/failure rate
            success_count = total_pages - failed_count
            if failed_count == 0:
                self.root.after(0, lambda: self.status_var.set(f"Ready - {success_count} pages loaded"))
            else:
                self.root.after(0, lambda: self.status_var.set(f"Ready - {success_count}/{total_pages} pages loaded"))
            
        except Exception as e:
            # Log error to console but don't show popup
            pass
            self.root.after(0, lambda: self.status_var.set("Error generating thumbnails - check console"))
            self.root.after(0, lambda: self.progress_bar.grid_remove())
            
    def display_thumbnails(self, force_rebuild=False):
        """Display thumbnail images in the canvas"""
        # Clear existing thumbnails if force_rebuild or first time
        if force_rebuild or not hasattr(self, '_thumbnails_displayed'):
            for widget in self.thumbnails_frame.winfo_children():
                widget.destroy()
            self.page_widgets.clear()
            self._thumbnails_displayed = False
        
        if not self.page_thumbnails:
            return
            
        # Calculate grid layout based on view mode
        canvas_width = self.canvas.winfo_width()
        if canvas_width <= 1:
            self.root.after(100, self.display_thumbnails)  # Retry when canvas is ready
            return
            
        margin = 15 if self.view_mode == 'single' else 10
        
        if self.view_mode == 'single':
            # Single page mode - force 1 column, larger spacing
            cols = 1
            thumb_width = min(self.thumbnail_size, canvas_width - 2 * margin)
        else:
            # Grid mode - calculate columns based on thumbnail size
            thumb_width = self.thumbnail_size + 60  # Add more padding for rotation buttons
            cols = max(1, (canvas_width - margin) // (thumb_width + margin))
        
        # Create thumbnail grid - display pages in current order, excluding deleted pages
        displayed_count = 0
        
        for display_position, original_page_index in enumerate(self.page_order):
            # Skip deleted pages
            if original_page_index in self.deleted_pages:
                continue
            
            # Validate page index
            if original_page_index >= len(self.page_thumbnails):
                continue
                
            # Get the thumbnail for this original page
            photo = self.page_thumbnails[original_page_index]
            
            # Skip if thumbnail failed to generate
            if photo is None:
                continue
                
            # Original page number (1-based for display)
            original_page_number = original_page_index + 1
            
            row = displayed_count // cols
            col = displayed_count % cols
            displayed_count += 1
            
            # In single page mode, center the thumbnail
            if self.view_mode == 'single':
                padx = margin
                sticky_opts = tk.N
            else:
                padx = margin//2
                sticky_opts = (tk.W, tk.E, tk.N, tk.S)
            
            # Create frame for each thumbnail
            bg_color = self.colors['edit_mode'] if self.edit_mode else self.colors['normal']
            thumb_frame = tk.Frame(self.thumbnails_frame, relief=tk.RAISED, borderwidth=2,
                                 bg=bg_color, cursor='hand2')
            thumb_frame.grid(row=row, column=col, padx=padx, pady=margin//2, 
                           sticky=sticky_opts)
            
            # Page number and rotation info
            rotation_angle = self.page_rotations.get(original_page_number, 0)
            rotation_text = f" (↻{rotation_angle}°)" if rotation_angle != 0 else ""
            
            # Show current position in edit mode
            if self.edit_mode:
                current_position = displayed_count  # 1-based position in current order
                page_text = f"#{current_position}: Page {original_page_number}{rotation_text}"
            else:
                page_text = f"Page {original_page_number}{rotation_text}"
            
            page_label = tk.Label(thumb_frame, text=page_text, 
                                font=(self.FONT_FAMILY, 11 if self.view_mode == 'single' else 9, 'bold'), 
                                bg=bg_color)
            page_label.pack(pady=(8 if self.view_mode == 'single' else 5, 
                                 2 if self.view_mode == 'single' else 1))
            
            # Edit mode controls (rotation and delete)
            if self.edit_mode:
                edit_controls_frame = tk.Frame(thumb_frame, bg=bg_color)
                edit_controls_frame.pack(pady=(0, 4 if self.view_mode == 'single' else 2))
                
                # Rotation buttons
                rotation_frame = tk.Frame(edit_controls_frame, bg=bg_color)
                rotation_frame.pack(side=tk.LEFT, padx=(0, 5))
                
                # Rotate left button
                rotate_left_btn = tk.Button(rotation_frame, text="↺", 
                                          font=(self.FONT_FAMILY, 10 if self.view_mode == 'single' else 8, 'bold'),
                                          width=3 if self.view_mode == 'single' else 2,
                                          height=1,
                                          command=lambda p=original_page_number: self.rotate_page(p, -90),
                                          bg='lightblue', relief=tk.RAISED, cursor='hand2')
                rotate_left_btn.pack(side=tk.LEFT, padx=(0, 2))
                
                # Rotate right button  
                rotate_right_btn = tk.Button(rotation_frame, text="↻", 
                                           font=(self.FONT_FAMILY, 10 if self.view_mode == 'single' else 8, 'bold'),
                                           width=3 if self.view_mode == 'single' else 2,
                                           height=1,
                                           command=lambda p=original_page_number: self.rotate_page(p, 90),
                                           bg='lightgreen', relief=tk.RAISED, cursor='hand2')
                rotate_right_btn.pack(side=tk.LEFT, padx=(2, 0))
                
                # Delete button - use display position to delete from current order
                delete_btn = tk.Button(edit_controls_frame, text="❌", 
                                     font=(self.FONT_FAMILY, 10 if self.view_mode == 'single' else 8, 'bold'),
                                     width=3 if self.view_mode == 'single' else 2,
                                     height=1,
                                     command=lambda pos=display_position: self.delete_page(pos),
                                     bg='lightcoral', relief=tk.RAISED, cursor='hand2')
                delete_btn.pack(side=tk.RIGHT)
            else:
                rotation_frame = None
                rotate_left_btn = None
                rotate_right_btn = None
                delete_btn = None
            
            # Thumbnail image
            thumb_label = tk.Label(thumb_frame, image=photo, bg=bg_color)
            thumb_label.pack(pady=(4 if self.view_mode == 'single' else 2, 
                                 4 if self.view_mode == 'single' else 2))
            
            # Status label (bottom)
            status_label = tk.Label(thumb_frame, text="", 
                                  font=(self.FONT_FAMILY, 10 if self.view_mode == 'single' else 8, 'bold'),
                                  bg=bg_color, fg='black')
            status_label.pack(pady=(0, 8 if self.view_mode == 'single' else 5))
            
            # Store widget references
            page_widget = {
                'frame': thumb_frame,
                'page_label': page_label,
                'thumb_label': thumb_label,
                'status_label': status_label,
                'rotation_frame': rotation_frame,
                'rotate_left_btn': rotate_left_btn,
                'rotate_right_btn': rotate_right_btn,
                'delete_btn': delete_btn if self.edit_mode else None,
                'page_num': original_page_number,  # 1-based page number for display
                'page_index': original_page_index,  # 0-based original page index
                'display_position': display_position  # Position in current page_order
            }
            
            # Add widget to the list (widgets are now stored in display order)
            self.page_widgets.append(page_widget)
            
            # Setup drag and drop if in edit mode (use display_position for the drag logic)
            if self.edit_mode:
                self.setup_drag_and_drop(page_widget, display_position)
            
            # Bind click events to main elements (not edit control buttons)
            clickable_widgets = [thumb_frame, page_label, thumb_label, status_label]
            if not self.edit_mode:  # Only bind regular clicks if not in edit mode
                for widget in clickable_widgets:
                    widget.bind(self.EVENT_BUTTON_1, lambda e, page=original_page_number: self.handle_click(e, page))
                    widget.bind('<B1-Motion>', lambda e, page=original_page_number: self.handle_drag(e, page))
                    widget.bind('<ButtonRelease-1>', lambda e, page=original_page_number: self.handle_release(e, page))
                    widget.bind('<Enter>', lambda e, page=original_page_number: self.on_page_hover(page, True))
                    widget.bind('<Leave>', lambda e, page=original_page_number: self.on_page_hover(page, False))
            else:
                # In edit mode, only bind hover effects to non-drag widgets
                for widget in clickable_widgets:
                    widget.bind('<Enter>', lambda e, page=original_page_number: self.on_page_hover(page, True))
                    widget.bind('<Leave>', lambda e, page=original_page_number: self.on_page_hover(page, False))
                    
            # Always bind mouse wheel scrolling
            for widget in clickable_widgets:
                widget.bind(self.EVENT_MOUSE_WHEEL, self.on_mousewheel)
                widget.bind(self.EVENT_BUTTON_4, self.on_mousewheel)  # Linux
                widget.bind(self.EVENT_BUTTON_5, self.on_mousewheel)  # Linux
        
        # Configure grid weights for single page mode
        if self.view_mode == 'single':
            self.thumbnails_frame.columnconfigure(0, weight=1)
        
        # Update scroll region and canvas size
        self.thumbnails_frame.update_idletasks()
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        
        # Mark thumbnails as successfully displayed
        self._thumbnails_displayed = True
        
        # Update selection display
        self.update_selection_display()
        
    def on_page_hover(self, page_num, enter):
        """Handle page hover effects"""
        # Find the widget for this page number in the current display order
        target_widget = None
        for widget in self.page_widgets:
            if widget is not None and widget['page_num'] == page_num:
                target_widget = widget
                break
                
        if not target_widget:
            return
            
        # Don't change color if page is selected or we're dragging
        if self.is_page_selected(page_num) or (self.drag_data and not self.drag_data.get('has_moved', False)):
            return
            
        if enter:
            self.set_page_color(target_widget, self.colors['hover'])
        else:
            bg_color = self.colors['edit_mode'] if self.edit_mode else self.colors['normal']
            self.set_page_color(target_widget, bg_color)
            
    def set_page_color(self, widget, color):
        """Set background color for all elements of a page widget"""
        elements_to_color = ['frame', 'page_label', 'thumb_label', 'status_label']
        if widget.get('rotation_frame'):
            elements_to_color.append('rotation_frame')
            
        for element in elements_to_color:
            if element in widget and widget[element]:
                widget[element].config(bg=color)
            
    def is_page_selected(self, page_num):
        """Check if a page is currently selected"""
        # Check if it's the current start page
        if self.current_selection['start'] == page_num:
            return True
            
        # Check if it's in any completed range
        for range_data in self.selected_ranges:
            if range_data['start'] <= page_num <= range_data['end']:
                return True
                
        return False
        
    def on_page_click(self, page_num):
        """Handle page thumbnail click"""
        if self.current_selection['start'] is None:
            # Start new selection
            self.current_selection['start'] = page_num
            self.current_selection['end'] = None
            self.status_var.set(f"Selected start page {page_num}. Click another page to complete range.")
            
        else:
            # Complete selection
            start = self.current_selection['start']
            end = page_num
            
            if end < start:
                start, end = end, start
                
            # Add to selected ranges with PDF file info
            pdf_filename = os.path.basename(self.pdf_path) if self.pdf_path else "Unknown"
            self.selected_ranges.append({
                'start': start, 
                'end': end,
                'pages': end - start + 1,
                'pdf_path': self.pdf_path,
                'pdf_filename': pdf_filename
            })
            
            self.update_ranges_list()
            
            # Reset for next selection
            self.current_selection = {'start': None, 'end': None}
            
            if start == end:
                self.status_var.set(f"Added single page {start}. Click another page to start new range.")
            else:
                self.status_var.set(f"Added pages {start}-{end}. Click another page to start new range.")
            
        self.update_selection_display()
        
    def update_selection_display(self):
        """Update visual selection indicators"""
        if not self.page_widgets:
            return
            
        # Reset all pages to normal
        for widget in self.page_widgets:
            if widget is None:  # Skip failed thumbnails
                continue
                
            page_num = widget['page_num']
            
            if not self.is_page_selected(page_num):
                bg_color = self.colors['edit_mode'] if self.edit_mode else self.colors['normal']
                self.set_page_color(widget, bg_color)
                widget['status_label'].config(text="", fg='black')
                widget['frame'].config(borderwidth=2, relief=tk.RAISED)
            
        # Show current selection start
        if self.current_selection['start']:
            # Find widget for start page
            start_widget = None
            for widget in self.page_widgets:
                if widget is not None and widget['page_num'] == self.current_selection['start']:
                    start_widget = widget
                    break
                    
            if start_widget:
                self.set_page_color(start_widget, self.colors['start'])
                start_widget['status_label'].config(text="START", fg='darkgreen')
                start_widget['frame'].config(borderwidth=3, relief=tk.SOLID)
            
        # Show completed ranges
        for range_data in self.selected_ranges:
            # Only show ranges for the current PDF
            if range_data.get('pdf_path') != self.pdf_path:
                continue
                
            for page in range(range_data['start'], range_data['end'] + 1):
                # Find widget for this page
                page_widget = None
                for widget in self.page_widgets:
                    if widget is not None and widget['page_num'] == page:
                        page_widget = widget
                        break
                        
                if not page_widget:
                    continue  # Skip if thumbnail failed or page not found
                    
                if page == range_data['start'] and page == range_data['end']:
                    # Single page
                    self.set_page_color(page_widget, self.colors['start'])
                    page_widget['status_label'].config(text="SINGLE", fg='darkgreen')
                    page_widget['frame'].config(borderwidth=3, relief=tk.SOLID)
                elif page == range_data['start']:
                    # Start of range
                    self.set_page_color(page_widget, self.colors['start'])
                    page_widget['status_label'].config(text="START", fg='darkgreen')
                    page_widget['frame'].config(borderwidth=3, relief=tk.SOLID)
                elif page == range_data['end']:
                    # End of range
                    self.set_page_color(page_widget, self.colors['end'])
                    page_widget['status_label'].config(text="END", fg='darkred')
                    page_widget['frame'].config(borderwidth=3, relief=tk.SOLID)
                else:
                    # Middle of range
                    self.set_page_color(page_widget, self.colors['selected'])
                    page_widget['status_label'].config(text="SELECTED", fg='darkorange')
                    page_widget['frame'].config(borderwidth=3, relief=tk.SOLID)
                    
    def on_range_tree_click(self, event):
        """Handle clicks on the ranges tree, especially delete buttons"""
        item = self.ranges_tree.identify('item', event.x, event.y)
        column = self.ranges_tree.identify('column', event.x, event.y)
        
        if item and column == '#1':  # Delete column
            # Get the index of the clicked item
            all_items = self.ranges_tree.get_children()
            index = all_items.index(item)
            
            # Remove the range
            if 0 <= index < len(self.selected_ranges):
                removed_range = self.selected_ranges[index]
                del self.selected_ranges[index]
                
                self.update_ranges_list()
                self.update_selection_display()
                
                self.status_var.set(f"Removed range: pages {removed_range['start']}-{removed_range['end']}")
                
    def update_ranges_list(self):
        """Update the selected ranges list with individual delete buttons"""
        # Clear existing items
        for item in self.ranges_tree.get_children():
            self.ranges_tree.delete(item)
            
        # Add current ranges
        total_pages = 0
        for range_data in self.selected_ranges:
            start, end, pages = range_data['start'], range_data['end'], range_data['pages']
            pdf_filename = range_data.get('pdf_filename', 'Unknown')
            total_pages += pages
            
            if start == end:
                range_text = f"Page {start}"
            else:
                range_text = f"Pages {start}-{end}"
                
            # Insert with delete button in first column
            self.ranges_tree.insert("", tk.END, values=("❌", range_text, pages, pdf_filename))
            
        # Update count
        range_count = len(self.selected_ranges)
        if range_count == 0:
            self.range_count_var.set("0 ranges selected")
        else:
            self.range_count_var.set(f"{range_count} ranges ({total_pages} total pages)")
            
    def remove_selected_range(self):
        """Remove selected range from list"""
        selection = self.ranges_tree.selection()
        if not selection:
            messagebox.showinfo("Info", "Please select a range to remove.")
            return
            
        index = self.ranges_tree.index(selection[0])
        removed_range = self.selected_ranges[index]
        del self.selected_ranges[index]
        
        self.update_ranges_list()
        self.update_selection_display()
        
        self.status_var.set(f"Removed range: pages {removed_range['start']}-{removed_range['end']}")
        
    def rotate_page(self, page_number, angle):
        """Rotate a specific page by the given angle"""
        
        # Update rotation for this page
        current_rotation = self.page_rotations.get(page_number, 0)
        new_rotation = (current_rotation + angle) % 360
        
        if new_rotation == 0:
            # Remove from dictionary if back to 0
            self.page_rotations.pop(page_number, None)
        else:
            self.page_rotations[page_number] = new_rotation
        
        
        # Update status
        if new_rotation == 0:
            self.status_var.set(f"Page {page_number} rotation reset")
        else:
            self.status_var.set(f"Page {page_number} rotated to {new_rotation}°")
        
        # Regenerate the affected thumbnail and refresh display
        self.regenerate_single_thumbnail(page_number)
        
        # Refresh the display to show updated rotation
        self.display_thumbnails(force_rebuild=True)
        
    def regenerate_single_thumbnail(self, page_number):
        """Regenerate thumbnail for a single page"""
        try:
            page_index = page_number - 1  # Convert to 0-based index
            
            if page_index < 0 or page_index >= len(self.pdf_document):
                return
                
            # Render the specific page
            page = self.pdf_document[page_index]
            
            # Calculate zoom factor
            page_rect = page.rect
            zoom = self.thumbnail_size / max(page_rect.width, page_rect.height)
            mat = fitz.Matrix(zoom, zoom)
            
            # Apply rotation if set for this page
            if page_number in self.page_rotations:
                rotation_angle = self.page_rotations[page_number]
                mat = mat.prerotate(rotation_angle)  # Use prerotate instead of matrix multiplication
            
            # Render page
            pix = page.get_pixmap(matrix=mat)
            img_data = pix.tobytes("ppm")
            
            # Create PIL image and convert to PhotoImage
            img = Image.open(io.BytesIO(img_data))
            photo = ImageTk.PhotoImage(img)
            
            # Update the thumbnail in the list at the original page index
            self.page_thumbnails[page_index] = photo
            
            # Note: Individual widget updating is handled by the display_thumbnails() call
            # in rotate_page() function with force_rebuild=True
                
        except Exception as e:
            pass
            # Don't show error dialog for single thumbnail failures
            
    def clear_ranges_only(self):
        """Clear only the page ranges, leaving crops intact"""
        if not self.selected_ranges:
            messagebox.showinfo("Info", "No ranges to clear.")
            return
            
        range_count = len(self.selected_ranges)
        if messagebox.askyesno("Clear Ranges", f"Clear all {range_count} selected page ranges?"):
            self.current_selection = {'start': None, 'end': None}
            self.selected_ranges.clear()
            
            self.update_ranges_list()
            self.update_selection_display()
            
            self.status_var.set("All page ranges cleared")
        
    def clear_selection(self):
        """Clear all selections and crops if in crop mode"""
        self.current_selection = {'start': None, 'end': None}
        self.selected_ranges.clear()
        
        # Also clear crops if in crop mode
        if self.crop_mode and self.crop_rectangles:
            self.crop_rectangles.clear()
            self.crop_thumbnails.clear()
            self.crop_counter = 0
            
        self.update_ranges_list()
        self.update_selection_display()
        self.update_crop_display()
        
        if self.crop_mode and self.crop_rectangles:
            self.status_var.set("All selections and crops cleared")
        else:
            self.status_var.set("All selections cleared")
        
    def clear_all_rotations(self):
        """Clear all page rotations"""
        if not self.page_rotations:
            messagebox.showinfo("Info", "No rotations to clear.")
            return
            
        if messagebox.askyesno("Clear Rotations", 
                             f"Reset rotation for {len(self.page_rotations)} pages?"):
            self.page_rotations.clear()
            self.status_var.set("All rotations cleared")
            # Regenerate all thumbnails
            if self.pdf_document:
                threading.Thread(target=self.generate_thumbnails, daemon=True).start()
        
    def zoom_in(self):
        """Increase thumbnail size"""
        new_size = min(self.max_zoom, self.thumbnail_size + self.zoom_step)
        self.zoom_var.set(new_size)
        self.on_zoom_change(new_size)
        
    def zoom_out(self):
        """Decrease thumbnail size"""
        new_size = max(self.min_zoom, self.thumbnail_size - self.zoom_step)
        self.zoom_var.set(new_size)
        self.on_zoom_change(new_size)
        
    def reset_zoom(self):
        """Reset zoom to default"""
        self.zoom_var.set(150)
        self.on_zoom_change(150)
        
    def set_single_page_view(self):
        """Switch to single page view mode (called automatically by zoom)"""
        self.view_mode = 'single'
        if self.page_thumbnails:
            self.status_var.set("Updating view mode...")
            threading.Thread(target=self.generate_thumbnails, daemon=True).start()
        
    def set_grid_view(self):
        """Switch to grid view mode (called automatically by zoom)"""
        self.view_mode = 'grid'
        if self.page_thumbnails:
            self.status_var.set("Updating view mode...")
            threading.Thread(target=self.generate_thumbnails, daemon=True).start()
        
    def on_zoom_change(self, value):
        """Handle zoom slider change with automatic view mode switching"""
        new_size = int(float(value))
        if new_size == self.thumbnail_size:
            return
            
        self.thumbnail_size = new_size
        self.zoom_label.config(text=f"{new_size}px")
        
        # Automatic view mode switching based on zoom level
        previous_view_mode = self.view_mode
        if new_size >= 500:
            self.view_mode = 'single'
        else:
            self.view_mode = 'grid'
            
        # Update status if view mode changed
        if previous_view_mode != self.view_mode:
            view_name = "Single Page" if self.view_mode == 'single' else "Grid"
            self.status_var.set(f"Switched to {view_name} view (zoom: {new_size}px)")
        
        # Regenerate thumbnails if PDF is loaded
        if self.pdf_document:
            if previous_view_mode != self.view_mode:
                self.status_var.set(f"Updating to {view_name} view...")
                # Only do full regeneration when view mode changes
                threading.Thread(target=self.generate_thumbnails, daemon=True).start()
            else:
                self.status_var.set("Updating thumbnail size...")
                # For size-only changes, just regenerate existing thumbnails more efficiently
                threading.Thread(target=self.regenerate_thumbnails_for_zoom, daemon=True).start()
            
    def regenerate_thumbnails_for_zoom(self):
        """Efficiently regenerate thumbnails for zoom changes without losing state"""
        if not self.pdf_document or not self.page_thumbnails:
            return
            
        try:
            total_pages = len(self.pdf_document)
            
            # Generate new thumbnails at the new size - keep original page indexing
            new_thumbnails = [None] * total_pages
            
            for page_num in range(total_pages):
                try:
                    # Show progress
                    self.root.after(0, lambda p=page_num, t=total_pages: 
                                   self.status_var.set(f"Updating thumbnails... {p+1}/{t}"))
                    
                    page = self.pdf_document[page_num]
                    page_rect = page.rect
                    
                    # Calculate zoom factor to fit thumbnail size
                    zoom = self.thumbnail_size / max(page_rect.width, page_rect.height)
                    
                    # Get rotation for this page (use 1-based page number for rotations)
                    rotation = self.page_rotations.get(page_num + 1, 0)
                    
                    # Create image with proper rotation
                    mat = fitz.Matrix(zoom, zoom).prerotate(rotation)
                    pix = page.get_pixmap(matrix=mat)
                    img_data = pix.tobytes("ppm")
                    img = Image.open(io.BytesIO(img_data))
                    
                    # Convert to PhotoImage
                    photo = ImageTk.PhotoImage(img)
                    new_thumbnails[page_num] = photo
                    
                except Exception as e:
                    pass
                    new_thumbnails[page_num] = None
            
            # Update thumbnails list - maintain original page indexing
            self.page_thumbnails = new_thumbnails
            
            # Update display with the new thumbnails
            self.root.after(0, lambda: self.display_thumbnails(force_rebuild=True))
            self.root.after(0, lambda: self.status_var.set("Thumbnails updated"))
            
        except Exception as e:
            pass
            self.root.after(0, lambda: self.status_var.set("Error updating thumbnails"))
            
    def split_and_save(self):
        """Split PDF and save selected ranges"""
        
        if not self.pdf_document and not self.pdf_list:
            messagebox.showwarning("Warning", "Please load a PDF file or folder first.")
            return
            
        if not self.selected_ranges:
            messagebox.showwarning("Warning", "Please select at least one page range first.")
            return
            
        
        # Get filename choice from user
        try:
            if len(self.pdf_list) == 1:
                default_name = Path(self.pdf_list[0]).stem + "_split.zip"
            else:
                default_name = "multi_pdf_split.zip"
        except:
            default_name = "split_pdf.zip"
        
        chosen_filename = self.get_custom_filename(default_name, "ZIP")
        if not chosen_filename:
            return
            
        
        save_path = filedialog.asksaveasfilename(
            title="Save Split PDF as ZIP",
            defaultextension=".zip",
            initialfile=chosen_filename,
            filetypes=[("ZIP files", "*.zip"), ("All files", "*.*")]
        )
        
        
        if not save_path:
            return
            
        # Split directly in main thread for debugging
        self._split_pdf_direct(save_path)
        
    def _split_pdf_direct(self, save_path):
        """Split PDF directly (for debugging)"""
        try:
            
            # Show progress bar
            self.progress_bar.grid(row=3, column=0, sticky=(tk.W, tk.E), pady=(10, 0))
            self.status_var.set("Splitting PDF...")
            self.progress_var.set(0)
            self.root.update()
            
            # Create ZIP file
            with zipfile.ZipFile(save_path, 'w', zipfile.ZIP_DEFLATED) as zip_file:
                total_ranges = len(self.selected_ranges)
                
                for i, range_data in enumerate(self.selected_ranges):
                    start_page = range_data['start'] - 1  # Convert to 0-indexed
                    end_page = range_data['end'] - 1
                    pdf_source_path = range_data['pdf_path']
                    
                    
                    # Update progress
                    progress = (i / total_ranges) * 90
                    self.progress_var.set(progress)
                    self.status_var.set(f"Processing range {i+1}/{total_ranges}...")
                    self.root.update()
                    
                    # Read the source PDF
                    with open(pdf_source_path, 'rb') as file:
                        pdf_reader = PyPDF2.PdfReader(file)
                        total_pdf_pages = len(pdf_reader.pages)
                        
                        # Validate range
                        if start_page < 0 or end_page >= total_pdf_pages or start_page > end_page:
                            continue
                        
                        # Create new PDF for this range
                        pdf_writer = PyPDF2.PdfWriter()
                        
                        for page_num in range(start_page, end_page + 1):
                            if page_num < total_pdf_pages:
                                page = pdf_reader.pages[page_num]
                                
                                # Apply rotation if set for this page (1-based)
                                page_number_1based = page_num + 1
                                if page_number_1based in self.page_rotations and pdf_source_path == self.pdf_path:
                                    rotation_angle = self.page_rotations[page_number_1based]
                                    if rotation_angle == 90:
                                        page = page.rotate(90)
                                    elif rotation_angle == 180:
                                        page = page.rotate(180)
                                    elif rotation_angle == 270:
                                        page = page.rotate(270)
                                
                                pdf_writer.add_page(page)
                        
                        # Write PDF to memory
                        pdf_buffer = io.BytesIO()
                        pdf_writer.write(pdf_buffer)
                        pdf_buffer.seek(0)
                        pdf_data = pdf_buffer.getvalue()
                        
                        
                        # Generate filename
                        try:
                            base_name = Path(pdf_source_path).stem
                        except:
                            base_name = f"document_{i+1}"
                            
                        if start_page == end_page:
                            filename = f"{base_name}_page_{start_page + 1}.pdf"
                        else:
                            filename = f"{base_name}_pages_{start_page + 1}-{end_page + 1}.pdf"
                        
                        
                        # Add to ZIP
                        zip_file.writestr(filename, pdf_data)
                        
            # Complete
            self.progress_var.set(100)
            self.status_var.set("PDF split successfully!")
            self.root.update()
            
            
            messagebox.showinfo("Success", 
                f"PDF split into {len(self.selected_ranges)} files successfully!\n\n"
                f"Saved to:\n{save_path}\n\n"
                f"Files created: {len(self.selected_ranges)} PDFs in ZIP")
            
        except Exception as e:
            import traceback
            traceback.print_exc()  # Debug
            
            messagebox.showerror("Error", 
                f"Failed to split PDF:\n\n{str(e)}\n\nCheck the console for more details.")
            self.status_var.set("Error splitting PDF")
        finally:
            # Hide progress bar
            self.progress_bar.grid_remove()
            
    def on_canvas_configure(self, event):
        """Handle canvas resize"""
        # Update the canvas window width to match canvas width
        canvas_width = event.width
        self.canvas.itemconfig(self.canvas_window, width=canvas_width)
        
        # Trigger thumbnail redisplay for new layout
        if self.page_thumbnails and hasattr(self, 'thumbnails_frame'):
            self.root.after(100, self.display_thumbnails)
                
    def on_frame_configure(self, event):
        """Handle thumbnails frame resize"""
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        
    def get_custom_filename(self, default_name, file_type="PDF", pattern_preview=None):
        """Show dialog to choose between default or custom filename
        
        Args:
            default_name: The default filename the app would use
            file_type: Type of file being saved (PDF, ZIP, etc.)
            pattern_preview: For multi-file saves, show pattern preview
            
        Returns:
            str: Chosen filename, or None if cancelled
        """
        dialog = tk.Toplevel(self.root)
        dialog.title(f"Choose {file_type} Filename")
        dialog.geometry("500x300")
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Center the dialog
        dialog.update_idletasks()
        x = (dialog.winfo_screenwidth() // 2) - (dialog.winfo_width() // 2)
        y = (dialog.winfo_screenheight() // 2) - (dialog.winfo_height() // 2)
        dialog.geometry(f"+{x}+{y}")
        
        result = {"filename": None}
        
        # Main frame
        main_frame = ttk.Frame(dialog, padding="20")
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # Title
        ttk.Label(main_frame, text=f"How do you want to name your {file_type} file?", 
                 font=(self.FONT_FAMILY, 12, "bold")).pack(pady=(0, 15))
        
        # Choice variable
        choice_var = tk.StringVar(value="default")
        
        # Default option
        default_frame = ttk.Frame(main_frame)
        default_frame.pack(fill=tk.X, pady=5)
        
        ttk.Radiobutton(default_frame, text="Use default naming:", 
                       variable=choice_var, value="default").pack(anchor=tk.W)
        
        default_label = ttk.Label(default_frame, text=default_name, 
                                 font=(self.FONT_FAMILY, 9), foreground="blue")
        default_label.pack(anchor=tk.W, padx=(25, 0))
        
        if pattern_preview:
            pattern_label = ttk.Label(default_frame, text=pattern_preview, 
                                    font=(self.FONT_FAMILY, 8), foreground="gray")
            pattern_label.pack(anchor=tk.W, padx=(25, 0))
        
        # Separator
        ttk.Separator(main_frame, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=15)
        
        # Custom option
        custom_frame = ttk.Frame(main_frame)
        custom_frame.pack(fill=tk.X, pady=5)
        
        ttk.Radiobutton(custom_frame, text="Use custom name:", 
                       variable=choice_var, value="custom").pack(anchor=tk.W)
        
        # Custom input
        input_frame = ttk.Frame(custom_frame)
        input_frame.pack(fill=tk.X, padx=(25, 0), pady=5)
        
        custom_entry = ttk.Entry(input_frame, font=(self.FONT_FAMILY, 10))
        custom_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        
        # Set default custom name (without extension)
        base_name = Path(default_name).stem
        custom_entry.insert(0, base_name)
        
        # Extension label
        ext = Path(default_name).suffix
        ttk.Label(input_frame, text=ext, font=(self.FONT_FAMILY, 10)).pack(side=tk.LEFT, padx=(5, 0))
        
        # Buttons
        button_frame = ttk.Frame(main_frame)
        button_frame.pack(fill=tk.X, pady=(20, 0))
        
        def on_ok():
            if choice_var.get() == "default":
                result["filename"] = default_name
            else:
                custom_name = custom_entry.get().strip()
                if not custom_name:
                    messagebox.showwarning("Warning", "Please enter a custom filename.")
                    return
                # Add extension if not present
                if not custom_name.endswith(ext):
                    custom_name += ext
                result["filename"] = custom_name
            dialog.destroy()
        
        def on_cancel():
            dialog.destroy()
        
        ttk.Button(button_frame, text="Cancel", command=on_cancel).pack(side=tk.RIGHT, padx=(5, 0))
        ttk.Button(button_frame, text="OK", command=on_ok).pack(side=tk.RIGHT)
        
        # Enable custom entry when custom radio is selected
        def on_choice_change():
            if choice_var.get() == "custom":
                custom_entry.config(state=tk.NORMAL)
                custom_entry.focus_set()
                custom_entry.select_range(0, tk.END)
            else:
                custom_entry.config(state=tk.DISABLED)
        
        choice_var.trace_add("write", lambda *args: on_choice_change())
        on_choice_change()  # Initial state
        
        # Handle Enter key
        dialog.bind('<Return>', lambda e: on_ok())
        dialog.bind('<Escape>', lambda e: on_cancel())
        
        dialog.wait_window()
        return result["filename"]
    
    def show_help(self):
        """Show help dialog"""
        help_text = """Visual PDF Splitter with Edit Mode - How to Use

🚀 QUICK START:
1. Click "Select PDF File" or "Select Folder" to load documents
2. Wait for page thumbnails to appear
3. Select pages for splitting OR use crop mode for area extraction OR edit pages
4. Click "Split & Save ZIP", extract crops, or save edited PDF

📁 FOLDER MODE:
• Select a folder containing multiple PDF files
• Use ⬅️➡️ keys to navigate between PDFs
• Use ⬆️⬇️ keys to scroll through pages
• Select ranges from any PDF in the folder

✏️ EDIT MODE:
• Toggle "✏️ Edit Mode" to enable comprehensive page editing
• Drag any page thumbnail to rearrange pages
• Click ❌ button on pages to delete them
• Use ↺↻ rotation buttons to rotate pages (only available in edit mode)
• Drop between pages to insert at that position
• Blue highlighting shows valid drop zones during drag
• Page numbers show current position (e.g., "#1: Page 5" means Page 5 is now in position 1)
• Deleted pages are removed from the document entirely
• Click "Reset" to restore original order, deleted pages, and rotations
• Click "Save PDF" to save all edits (reorder, deletions, rotations) as a new PDF file
• Edit mode consolidates all page modification operations

✂️ CROP MODE:
• Toggle crop mode with "✂️ Crop Mode" checkbox
• Drag on page thumbnails to select rectangular areas
• Multiple crops per page supported
• Extract crops as PDF files (vector quality) or PNG images (raster)
• Automatic filename generation with page and crop numbers
• Preview crops in the right panel with individual delete buttons

📖 PAGE SELECTION:
• First click: Sets START of range (green)
• Second click: Sets END of range (red) 
• Pages between: Automatically selected (yellow)
• Same page twice: Single page selection
• Individual ❌ buttons: Click to delete specific ranges

🎯 OPERATION EXAMPLES:
• Pages 1-10: Click page 1, then click page 10
• Single page 5: Click page 5, then click page 5 again
• Multiple ranges: Complete one range, then start another
• Delete specific range: Click ❌ button next to the range
• Crop areas: Enable crop mode, drag on thumbnails to select regions
• Reorder pages: Enable edit mode, drag pages to new positions
• Delete pages: Enable edit mode, click ❌ on pages to remove them
• Rotate pages: Enable edit mode, use ↺↻ buttons

🛠️ CONTROLS:
• Thumbnail Size: Use slider, +/- buttons, or Ctrl+Mouse Wheel (up to 1600px!)
• Automatic View Switching: Grid view under 500px, Single view at 500px+
• Mouse wheel: Scroll through pages
• Ctrl+Mouse wheel: Zoom in/out (like web browsers)
• Clear Ranges: Remove page ranges (in Selected Ranges panel)
• Clear Crops: Remove crop rectangles (in Crop Previews panel)
• Reset: Restore original order, deleted pages, and rotations (edit mode)
• Individual Delete: Click ❌ buttons next to ranges/crops to remove specific items

⌨️ KEYBOARD SHORTCUTS:
• Ctrl+O: Open PDF file
• Ctrl+Shift+O: Open folder
• Ctrl+C: Clear all selections
• Ctrl+R: Reset edit session (restore all changes)
• Ctrl+S: Save edited PDF
• Ctrl+T: Toggle crop mode
• Ctrl+E: Toggle edit mode
• Ctrl+P: Extract crops as PDF
• Ctrl+G: Extract crops as PNG
• Ctrl++/Ctrl+-: Zoom in/out
• Ctrl+Mouse Wheel: Zoom in/out (like web browsers)
• Ctrl+0: Reset zoom
• ⬆️⬇️: Navigate between PDFs (folder mode)
• ⬅️➡️: Scroll through pages
• F1: Show this help

🎨 VISUAL INDICATORS:
🟢 Green border + "START": Beginning of range
🔴 Red border + "END": End of range
🟡 Yellow border + "SELECTED": Pages in range
🔵 Blue hover: Page you're about to click
🟠 Orange: Page being dragged (edit mode)
🔵 Blue highlight: Valid drop zone (edit mode)
🟣 Lavender background: Edit mode active
✂️ Crosshair cursor: Crop mode active
✏️ Position numbers: Current page order (e.g., "#2: Page 7")
❌ Delete buttons: Remove pages or crops
↺↻ Rotation buttons: Only visible in edit mode

📦 OUTPUT OPTIONS:
• Split PDFs: Creates ZIP with separate PDFs for each range
• Crop PDFs: Creates individual PDF files for each crop area
• Crop PNGs: Creates PNG images for each crop area
• Edited PDF: Saves current page order with deletions and rotations applied
• Automatic filename generation with source info
• Preserves original PDF quality and applies all edits

💡 TIPS:
• Zoom automatically switches view modes (Grid < 500px, Single ≥ 500px)
• Larger thumbnails help identify pages and make editing/cropping easier
• You can select overlapping ranges
• Crop mode works best with zoomed-in thumbnails
• Edit mode consolidates all page editing in one place
• Right panel shows selected ranges and crop previews with more space
• Click ❌ buttons for quick individual removal of ranges/crops/pages
• Navigation buttons appear when multiple PDFs loaded
• Edit changes are preserved when switching between crop/selection modes
• Page rotations only work in edit mode for consistency
• Deleted pages are completely removed from the final document

⚠️ IMPORTANT NOTES:
• Only one mode can be active at a time (Selection, Crop, or Edit)
• Editing only affects the current PDF (not folder-wide)
• Original PDF is never modified - all operations create new files
• Edited pages maintain their formatting
• Page numbers in edit view show both position and original page
• Deleted pages cannot be recovered except by clicking "Reset"
• Rotation buttons only appear in edit mode

⚠️ REQUIREMENTS:
• PDF files only (no password protection)
• Minimum 16MB free disk space
• At least one page range, crop area, or edit operation must be performed"""
        
        help_window = tk.Toplevel(self.root)
        help_window.title("Help - Visual PDF Splitter with Edit Mode")
        help_window.geometry("700x600")
        help_window.resizable(True, True)
        
        # Make window modal
        help_window.transient(self.root)
        help_window.grab_set()
        
        # Center the window
        help_window.geometry("+%d+%d" % (
            self.root.winfo_rootx() + 50,
            self.root.winfo_rooty() + 50
        ))
        
        # Create scrollable text widget
        text_frame = ttk.Frame(help_window)
        text_frame.pack(fill=tk.BOTH, expand=True, padx=15, pady=15)
        
        text_widget = scrolledtext.ScrolledText(text_frame, wrap=tk.WORD, 
                                              font=(self.FONT_FAMILY, 10), padx=10, pady=10)
        text_widget.pack(fill=tk.BOTH, expand=True)
        text_widget.insert(tk.END, help_text)
        text_widget.config(state=tk.DISABLED)
        
        # Close button
        button_frame = ttk.Frame(help_window)
        button_frame.pack(fill=tk.X, padx=15, pady=(0, 15))
        
        ttk.Button(button_frame, text="Close", command=help_window.destroy,
                  style=self.STYLE_ACCENT_BUTTON).pack(side=tk.RIGHT)
        
    def show_about(self):
        """Show about dialog"""
        about_text = """Visual PDF Splitter with Edit Mode v5.1

A powerful desktop application for splitting PDF files with visual page selection, thumbnail previews, comprehensive edit mode (drag & drop reordering + page deletion + rotation), multi-PDF folder support, and crop extraction functionality with enhanced visual feedback, browser-like zoom controls, and streamlined interface.

🔧 FEATURES:
• Visual page thumbnails for easy identification
• Click-to-select page ranges
• Comprehensive Edit Mode with drag & drop page reordering, deletion, and rotation
• Multiple range selection support
• Individual ❌ delete buttons for ranges, crops, and pages
• Contextual clear and reset functions
• Visual crop selection feedback with transparent overlay
• Browser-like zoom controls (Ctrl+Mouse Wheel)
• Clean, streamlined control interface with intelligent mode switching
• Folder-based PDF loading with navigation
• PDF navigation with arrow keys
• Adjustable thumbnail zoom (up to 1600px)
• Automatic view mode switching based on zoom level
• Crop mode for area extraction with real-time visual feedback
• Extract crops as PDF or PNG files
• Enhanced crop preview panel with more space
• ZIP file output with multiple PDFs
• Save edited PDFs with all modifications applied
• Modern, intuitive interface with visual mode indicators
• Enhanced keyboard shortcuts
• Progress tracking and status updates

💻 TECHNICAL INFO:
• Built with Python and tkinter
• Uses PyMuPDF for PDF rendering and cropping
• Uses PyPDF2 for PDF manipulation, reordering, and deletion
• Advanced drag & drop implementation with ghost images
• Comprehensive edit session management
• Cross-platform compatibility
• No internet connection required

👨‍💻 DEVELOPED BY:
Enhanced by Claude (Anthropic) with Comprehensive Edit Mode - December 2024

🆓 LICENSE:
Free for personal and commercial use

📧 SUPPORT:
For issues or questions, please refer to the documentation or contact support."""
        
        messagebox.showinfo("About Visual PDF Splitter with Edit Mode", about_text)

    # ===== CROP FUNCTIONALITY =====
    
    def toggle_crop_mode(self):
        """Toggle between page selection and crop mode"""
        self.crop_mode = self.crop_mode_var.get()
        
        if self.crop_mode:
            # Disable edit mode when entering crop mode
            if self.edit_mode:
                self.edit_mode_var.set(False)
                self.toggle_edit_mode()
                
            self.status_var.set("Crop mode enabled - Drag on pages to select areas with visual feedback")
            # Change cursor for crop mode
            self.canvas.config(cursor="crosshair")
        else:
            self.status_var.set("Page selection mode enabled")
            self.canvas.config(cursor="")
            # Clean up any active crop overlay
            self.remove_crop_overlay()
            
        # Update UI to reflect mode change
        self.update_crop_display()
        
    def handle_click(self, event, page_num):
        """Handle mouse click - route to appropriate handler based on mode"""
        if self.crop_mode:
            self.start_crop(event, page_num)
        else:
            self.on_page_click(page_num)
            
    def handle_drag(self, event, page_num):
        """Handle mouse drag - route to appropriate handler based on mode"""
        if self.crop_mode:
            self.update_crop(event, page_num)
            
    def handle_release(self, event, page_num):
        """Handle mouse release - route to appropriate handler based on mode"""
        if self.crop_mode:
            self.end_crop(event, page_num)
            
    def start_crop(self, event, page_num):
        """Start drawing a crop rectangle with visual feedback"""
        if not self.crop_mode:
            return
            
        # Get widget and convert coordinates
        widget = self.get_page_widget(page_num)
        if not widget:
            return
            
        # Store crop start position relative to the thumbnail image
        self.crop_start_pos = (event.x, event.y)
        self.current_crop = {
            'page': page_num,
            'start_x': event.x,
            'start_y': event.y,
            'widget': widget
        }
        
        # Create overlay canvas for visual feedback
        self.create_crop_overlay(widget, event.x, event.y)
        
    def create_crop_overlay(self, widget, start_x, start_y):
        """Create visual feedback for crop selection without blocking the PDF content"""
        thumb_label = widget['thumb_label']
        thumb_frame = widget['frame']
        
        # Instead of covering the image with a canvas, use frame borders for visual feedback
        # Store original frame appearance
        self.original_frame_relief = thumb_frame.cget('relief')
        self.original_frame_borderwidth = thumb_frame.cget('borderwidth')
        self.original_frame_bg = thumb_frame.cget('bg')
        
        # Make frame border red and thick to show crop mode is active
        thumb_frame.config(relief=tk.SOLID, borderwidth=4, bg='red')
        
        # Create corner indicators instead of overlay canvas to show crop area
        self.create_crop_corner_indicators(thumb_frame, thumb_label, start_x, start_y)
        
        # Update status
        page_num = widget['page_num']
        self.status_var.set(f"Drag to select crop area on page {page_num}")
        
    def create_crop_corner_indicators(self, thumb_frame, thumb_label, start_x, start_y):
        """Create small corner indicators to show crop selection without blocking content"""
        # Store reference for cleanup
        if not hasattr(self, 'crop_corner_widgets'):
            self.crop_corner_widgets = []
        
        # Create small red squares at corners to indicate selection area
        # These will be updated during drag operations
        corner_size = 6
        
        # Top-left corner indicator
        corner_tl = tk.Frame(thumb_frame, bg='red', width=corner_size, height=corner_size)
        corner_tl.place(x=start_x + thumb_label.winfo_x() - corner_size//2, 
                       y=start_y + thumb_label.winfo_y() - corner_size//2)
        self.crop_corner_widgets.append(corner_tl)
        
        # Store initial position for updates
        self.crop_start_corner_x = start_x + thumb_label.winfo_x()
        self.crop_start_corner_y = start_y + thumb_label.winfo_y()
        
    def update_crop(self, event, page_num):
        """Update crop visual feedback as user drags"""
        if not self.crop_mode or not self.current_crop or self.current_crop['page'] != page_num:
            return
        
        # Update corner indicators to show current selection area
        if hasattr(self, 'crop_corner_widgets') and self.crop_corner_widgets:
            # Clear existing corner indicators except the first one (start point)
            for widget in self.crop_corner_widgets[1:]:
                widget.destroy()
            self.crop_corner_widgets = self.crop_corner_widgets[:1]
            
            # Get widget info
            widget = self.get_page_widget(page_num)
            if not widget:
                return
                
            thumb_frame = widget['frame']
            thumb_label = widget['thumb_label']
            
            # Calculate current rectangle
            start_x = self.current_crop['start_x']
            start_y = self.current_crop['start_y']
            end_x = event.x
            end_y = event.y
            
            # Create corner indicators for current rectangle
            corner_size = 6
            label_x = thumb_label.winfo_x()
            label_y = thumb_label.winfo_y()
            
            # Add corner indicators at all four corners
            corners = [
                (end_x + label_x, start_y + label_y),  # top-right
                (start_x + label_x, end_y + label_y),  # bottom-left  
                (end_x + label_x, end_y + label_y)     # bottom-right
            ]
            
            for corner_x, corner_y in corners:
                corner = tk.Frame(thumb_frame, bg='red', width=corner_size, height=corner_size)
                corner.place(x=corner_x - corner_size//2, y=corner_y - corner_size//2)
                self.crop_corner_widgets.append(corner)
        
        # Store current coordinates
        self.current_crop.update({
            'end_x': event.x,
            'end_y': event.y
        })
        
        # Show dimensions in status
        start_x = self.current_crop['start_x']
        start_y = self.current_crop['start_y']
        width = abs(event.x - start_x)
        height = abs(event.y - start_y)
        self.status_var.set(f"Crop selection: {width}×{height} pixels - release to complete")
        
    def end_crop(self, event, page_num):
        """Complete crop rectangle and store it, remove visual feedback"""
        if not self.crop_mode or not self.current_crop or self.current_crop['page'] != page_num:
            return
            
        # Remove overlay visual feedback first
        self.remove_crop_overlay()
            
        # Calculate crop rectangle coordinates
        start_x = self.current_crop['start_x']
        start_y = self.current_crop['start_y']
        end_x = event.x
        end_y = event.y
        
        # Ensure we have a valid rectangle (minimum 10x10 pixels)
        if abs(end_x - start_x) < 10 or abs(end_y - start_y) < 10:
            self.current_crop = None
            self.status_var.set("Crop too small - minimum 10x10 pixels required")
            return
            
        # Normalize coordinates
        x1, x2 = min(start_x, end_x), max(start_x, end_x)
        y1, y2 = min(start_y, end_y), max(start_y, end_y)
        
        # Convert thumbnail coordinates to PDF page coordinates
        widget = self.current_crop['widget']
        thumb_label = widget['thumb_label']
        
        # Get thumbnail dimensions
        thumb_width = thumb_label.winfo_width()
        thumb_height = thumb_label.winfo_height()
        
        if thumb_width <= 1 or thumb_height <= 1:
            self.current_crop = None
            self.status_var.set("Could not determine thumbnail dimensions")
            return
            
        # Get actual page dimensions
        page_index = page_num - 1
        if page_index >= len(self.pdf_document):
            self.current_crop = None
            return
            
        page = self.pdf_document[page_index]
        page_rect = page.rect
        
        # Convert coordinates
        pdf_x1 = (x1 / thumb_width) * page_rect.width
        pdf_y1 = (y1 / thumb_height) * page_rect.height
        pdf_x2 = (x2 / thumb_width) * page_rect.width
        pdf_y2 = (y2 / thumb_height) * page_rect.height
        
        # Generate unique crop ID
        self.crop_counter += 1
        crop_id = f"crop_{self.crop_counter}"
        
        # Generate crop thumbnail image
        crop_thumbnail = self.generate_crop_thumbnail(page_num, pdf_x1, pdf_y1, pdf_x2, pdf_y2)
        
        # Store crop rectangle
        if page_num not in self.crop_rectangles:
            self.crop_rectangles[page_num] = []
            
        crop_data = {
            'id': crop_id,
            'pdf_coords': (pdf_x1, pdf_y1, pdf_x2, pdf_y2),
            'thumb_coords': (x1, y1, x2, y2),
            'pdf_path': self.pdf_path,
            'page_num': page_num,
            'thumbnail': crop_thumbnail
        }
        
        self.crop_rectangles[page_num].append(crop_data)
        
        # Store thumbnail for display
        if crop_thumbnail:
            self.crop_thumbnails[crop_id] = crop_thumbnail
        
        # Update display
        self.update_crop_display()
        
        # Update status
        crop_count = sum(len(crops) for crops in self.crop_rectangles.values())
        self.status_var.set(f"Crop added to page {page_num}. Total crops: {crop_count}")
        
        # Clear current crop
        self.current_crop = None

    def remove_crop_overlay(self):
        """Remove the crop selection visual feedback and restore normal appearance"""
        # Remove corner indicator widgets
        if hasattr(self, 'crop_corner_widgets'):
            for widget in self.crop_corner_widgets:
                widget.destroy()
            self.crop_corner_widgets = []
        
        # Clean up any old overlay canvas references (legacy)
        if hasattr(self, 'crop_overlay_canvas') and self.crop_overlay_canvas:
            self.crop_overlay_canvas.destroy()
            self.crop_overlay_canvas = None
            self.crop_overlay = None
        
        # Clean up any border frames (from previous approach)
        if hasattr(self, 'crop_border_frames'):
            for frame in self.crop_border_frames.values():
                frame.destroy()
            delattr(self, 'crop_border_frames')
        
        # Restore the frame styling
        if self.current_crop and 'widget' in self.current_crop:
            widget = self.current_crop['widget']
            thumb_frame = widget['frame']
            
            # Reset frame to original style
            try:
                thumb_frame.config(
                    relief=getattr(self, 'original_frame_relief', tk.RAISED),
                    borderwidth=getattr(self, 'original_frame_borderwidth', 2),
                    bg=getattr(self, 'original_frame_bg', 'SystemButtonFace')
                )
            except:
                # Fallback styling
                thumb_frame.config(relief=tk.RAISED, borderwidth=2, bg='SystemButtonFace', highlightbackground='')

    def generate_crop_thumbnail(self, page_num, pdf_x1, pdf_y1, pdf_x2, pdf_y2):
        """Generate a thumbnail image of the cropped area"""
        try:
            page_index = page_num - 1
            if page_index >= len(self.pdf_document):
                return None
                
            page = self.pdf_document[page_index]
            
            # Create crop rectangle
            crop_rect = fitz.Rect(pdf_x1, pdf_y1, pdf_x2, pdf_y2)
            
            # Render the cropped area at moderate resolution for thumbnail
            mat = fitz.Matrix(1.5, 1.5)  # 1.5x zoom for decent quality
            pix = page.get_pixmap(matrix=mat, clip=crop_rect)
            
            # Convert to PIL Image
            img_data = pix.tobytes("ppm")
            img = Image.open(io.BytesIO(img_data))
            
            # Resize to thumbnail size (max 120x120 while preserving aspect ratio)
            img.thumbnail((120, 120), Image.Resampling.LANCZOS)
            
            # Convert to PhotoImage
            photo = ImageTk.PhotoImage(img)
            
            return photo
            
        except Exception as e:
            pass
            return None
        
    def get_page_widget(self, page_num):
        """Get widget for a specific page number"""
        # Find widget with matching page number
        for widget in self.page_widgets:
            if widget is not None and widget['page_num'] == page_num:
                return widget
        return None
        
    def update_crop_display(self):
        """Update visual display of crop thumbnails in the preview panel"""
        # Clear existing crop thumbnails
        for widget in self.crop_thumbnails_frame.winfo_children():
            widget.destroy()
        
        # Count total crops
        total_crops = sum(len(crops) for crops in self.crop_rectangles.values())
        self.crop_count_var.set(f"{total_crops} crops")
        
        if total_crops == 0:
            # Show "no crops" message
            no_crops_label = tk.Label(self.crop_thumbnails_frame, 
                                    text="No crops selected\n\nEnable crop mode and drag on\npage thumbnails to create crops",
                                    font=(self.FONT_FAMILY, 10),
                                    fg='gray',
                                    bg='white',
                                    justify=tk.CENTER)
            no_crops_label.pack(expand=True, fill=tk.BOTH, pady=20)
            self.crop_canvas.configure(scrollregion=self.crop_canvas.bbox("all"))
            return
            
        # Display crop thumbnails
        row = 0
        for page_num, crops in self.crop_rectangles.items():
            # Only show crops for current PDF
            for crop_data in crops:
                if crop_data.get('pdf_path') != self.pdf_path:
                    continue
                    
                # Create frame for this crop
                crop_frame = tk.Frame(self.crop_thumbnails_frame, relief=tk.RAISED, 
                                    borderwidth=1, bg='white', padx=5, pady=5)
                crop_frame.grid(row=row, column=0, sticky=(tk.W, tk.E), padx=5, pady=2)
                
                # Configure grid weight
                self.crop_thumbnails_frame.columnconfigure(0, weight=1)
                
                # Crop info frame
                info_frame = tk.Frame(crop_frame, bg='white')
                info_frame.pack(fill=tk.X, pady=(0, 5))
                
                # Crop label
                crop_label = tk.Label(info_frame, 
                                    text=f"Page {page_num} - Crop {crops.index(crop_data) + 1}",
                                    font=(self.FONT_FAMILY, 9, 'bold'),
                                    bg='white')
                crop_label.pack(side=tk.LEFT)
                
                # Delete button
                delete_btn = tk.Button(info_frame, text="❌", 
                                     font=(self.FONT_FAMILY, 8),
                                     fg='red',
                                     bg='white',
                                     relief=tk.FLAT,
                                     cursor='hand2',
                                     command=lambda cid=crop_data['id']: self.delete_crop(cid))
                delete_btn.pack(side=tk.RIGHT, padx=(5, 0))
                
                # Thumbnail image
                if crop_data['thumbnail']:
                    thumb_label = tk.Label(crop_frame, 
                                         image=crop_data['thumbnail'], 
                                         bg='white',
                                         relief=tk.SOLID,
                                         borderwidth=1)
                    thumb_label.pack(pady=(0, 5))
                else:
                    # Fallback if thumbnail generation failed
                    placeholder_label = tk.Label(crop_frame,
                                                text="[Crop Preview]",
                                                font=(self.FONT_FAMILY, 8),
                                                fg='gray',
                                                bg='lightgray',
                                                width=15, height=8,
                                                relief=tk.SOLID,
                                                borderwidth=1)
                    placeholder_label.pack(pady=(0, 5))
                
                row += 1
        
        # Update scroll region
        self.crop_thumbnails_frame.update_idletasks()
        self.crop_canvas.configure(scrollregion=self.crop_canvas.bbox("all"))

    def delete_crop(self, crop_id):
        """Delete a specific crop by ID"""
        # Find and remove the crop
        for page_num, crops in self.crop_rectangles.items():
            for i, crop_data in enumerate(crops):
                if crop_data['id'] == crop_id:
                    # Remove from crops list
                    del crops[i]
                    
                    # Remove from thumbnails
                    if crop_id in self.crop_thumbnails:
                        del self.crop_thumbnails[crop_id]
                    
                    # Clean up empty page entries
                    if not crops:
                        del self.crop_rectangles[page_num]
                    
                    # Update display
                    self.update_crop_display()
                    
                    # Update status
                    total_crops = sum(len(c) for c in self.crop_rectangles.values())
                    self.status_var.set(f"Crop deleted. Total crops: {total_crops}")
                    
                    return
        
    def clear_all_crops(self):
        """Clear all crop rectangles"""
        if not self.crop_rectangles:
            messagebox.showinfo("Info", "No crops to clear.")
            return
            
        crop_count = sum(len(crops) for crops in self.crop_rectangles.values())
        if messagebox.askyesno("Clear Crops", f"Clear all {crop_count} crop rectangles?"):
            self.crop_rectangles.clear()
            self.crop_thumbnails.clear()
            self.crop_counter = 0
            self.update_crop_display()
            self.status_var.set("All crops cleared")
            
    def extract_crops_pdf(self):
        """Extract all crop rectangles as PDF files"""
        if not self.crop_rectangles:
            messagebox.showwarning("Warning", "No crop rectangles defined. Enter crop mode and select areas first.")
            return
            
        # Get custom base name choice from user
        if self.pdf_path:
            default_base = Path(self.pdf_path).stem
        else:
            default_base = "document"
        
        pattern_preview = f"Example: {default_base}_page_1_crop_1.pdf, {default_base}_page_1_crop_2.pdf, ..."
        chosen_base = self.get_custom_filename(default_base, "PDF", pattern_preview)
        if not chosen_base:
            return
        
        # Remove .pdf extension if user included it
        chosen_base = Path(chosen_base).stem
            
        # Get save directory
        save_dir = filedialog.askdirectory(title="Select Directory to Save Cropped PDFs")
        if not save_dir:
            return
            
        try:
            crop_count = 0
            for page_num, crops in self.crop_rectangles.items():
                page_index = page_num - 1
                
                for i, crop_data in enumerate(crops):
                    # Get crop coordinates
                    pdf_x1, pdf_y1, pdf_x2, pdf_y2 = crop_data['pdf_coords']
                    
                    # Open the source PDF
                    doc = fitz.open(crop_data['pdf_path'])
                    page = doc[page_index]
                    
                    # Create crop rectangle
                    crop_rect = fitz.Rect(pdf_x1, pdf_y1, pdf_x2, pdf_y2)
                    
                    # Crop the page
                    page.set_cropbox(crop_rect)
                    
                    # Create new PDF with cropped page
                    new_doc = fitz.open()
                    new_doc.insert_pdf(doc, from_page=page_index, to_page=page_index)
                    
                    # Generate filename using chosen base name
                    filename = f"{chosen_base}_page_{page_num}_crop_{i+1}.pdf"
                    save_path = os.path.join(save_dir, filename)
                    
                    # Save cropped PDF
                    new_doc.save(save_path)
                    new_doc.close()
                    doc.close()
                    
                    crop_count += 1
                    
            messagebox.showinfo("Success", f"Extracted {crop_count} crop regions as PDF files to:\n{save_dir}")
            self.status_var.set(f"Extracted {crop_count} crops as PDF files")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to extract crops as PDF:\n{str(e)}")
            
    def extract_crops_png(self):
        """Extract all crop rectangles as PNG files"""
        if not self.crop_rectangles:
            messagebox.showwarning("Warning", "No crop rectangles defined. Enter crop mode and select areas first.")
            return
            
        # Get custom base name choice from user
        if self.pdf_path:
            default_base = Path(self.pdf_path).stem
        else:
            default_base = "document"
        
        pattern_preview = f"Example: {default_base}_page_1_crop_1.png, {default_base}_page_1_crop_2.png, ..."
        chosen_base = self.get_custom_filename(default_base, "PNG", pattern_preview)
        if not chosen_base:
            return
        
        # Remove .png extension if user included it
        chosen_base = Path(chosen_base).stem
            
        # Get save directory
        save_dir = filedialog.askdirectory(title="Select Directory to Save Cropped PNG files")
        if not save_dir:
            return
            
        try:
            crop_count = 0
            for page_num, crops in self.crop_rectangles.items():
                page_index = page_num - 1
                
                for i, crop_data in enumerate(crops):
                    # Get crop coordinates
                    pdf_x1, pdf_y1, pdf_x2, pdf_y2 = crop_data['pdf_coords']
                    
                    # Open the source PDF
                    doc = fitz.open(crop_data['pdf_path'])
                    page = doc[page_index]
                    
                    # Create crop rectangle
                    crop_rect = fitz.Rect(pdf_x1, pdf_y1, pdf_x2, pdf_y2)
                    
                    # Render the cropped area at high resolution
                    mat = fitz.Matrix(2.0, 2.0)  # 2x zoom for better quality
                    pix = page.get_pixmap(matrix=mat, clip=crop_rect)
                    
                    # Generate filename using chosen base name
                    filename = f"{chosen_base}_page_{page_num}_crop_{i+1}.png"
                    save_path = os.path.join(save_dir, filename)
                    
                    # Save as PNG
                    pix.save(save_path)
                    doc.close()
                    
                    crop_count += 1
                    
            messagebox.showinfo("Success", f"Extracted {crop_count} crop regions as PNG files to:\n{save_dir}")
            self.status_var.set(f"Extracted {crop_count} crops as PNG files")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to extract crops as PNG:\n{str(e)}")

    def merge_two_pdfs(self):
        """Merge two PDFs from the loaded PDF list"""
        if len(self.pdf_list) < 2:
            messagebox.showwarning("Warning", "Please load at least two PDF files to merge.\nUse 'Open Folder' to load multiple PDFs or 'Add PDF' to merge with external file.")
            return
            
        # Create selection dialog for two PDFs
        self.show_pdf_merge_dialog()
        
    def merge_add_external(self):
        """Merge current PDF with an external PDF file"""
        if not self.pdf_document:
            messagebox.showwarning("Warning", "Please load a PDF file first.")
            return
            
        # Select external PDF file to merge with
        external_path = filedialog.askopenfilename(
            title="Select PDF to merge with current document",
            filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")]
        )
        
        if not external_path:
            return
            
        # Show merge order dialog
        self.show_external_merge_dialog(external_path)
        
    def show_pdf_merge_dialog(self):
        """Show dialog to select two PDFs from loaded list for merging"""
        dialog = tk.Toplevel(self.root)
        dialog.title("Merge Two PDFs")
        dialog.geometry("600x400")
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Center dialog
        dialog.geometry("+%d+%d" % (self.root.winfo_rootx() + 100, self.root.winfo_rooty() + 100))
        
        main_frame = ttk.Frame(dialog)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=20)
        
        ttk.Label(main_frame, text="Select Two PDFs to Merge", font=('Segoe UI', 12, 'bold')).pack(pady=(0, 10))
        ttk.Label(main_frame, text="Choose the order for merging:", font=('Segoe UI', 10)).pack(pady=(0, 10))
        
        # First PDF selection
        first_frame = ttk.Frame(main_frame)
        first_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(first_frame, text="First PDF:", font=('Segoe UI', 10, 'bold')).pack(anchor=tk.W)
        first_var = tk.StringVar()
        first_combo = ttk.Combobox(first_frame, textvariable=first_var, state='readonly', width=70)
        first_combo['values'] = [os.path.basename(pdf) for pdf in self.pdf_list]
        first_combo.pack(fill=tk.X, pady=(5, 0))
        
        # Second PDF selection
        second_frame = ttk.Frame(main_frame)
        second_frame.pack(fill=tk.X, pady=15)
        
        ttk.Label(second_frame, text="Second PDF:", font=('Segoe UI', 10, 'bold')).pack(anchor=tk.W)
        second_var = tk.StringVar()
        second_combo = ttk.Combobox(second_frame, textvariable=second_var, state='readonly', width=70)
        second_combo['values'] = [os.path.basename(pdf) for pdf in self.pdf_list]
        second_combo.pack(fill=tk.X, pady=(5, 0))
        
        # Set default selections if available
        if len(self.pdf_list) >= 2:
            first_combo.set(os.path.basename(self.pdf_list[0]))
            second_combo.set(os.path.basename(self.pdf_list[1]))
        
        # Preview frame
        preview_frame = ttk.LabelFrame(main_frame, text="Merge Preview", padding=10)
        preview_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        
        preview_text = tk.Text(preview_frame, height=8, wrap=tk.WORD, state=tk.DISABLED)
        preview_text.pack(fill=tk.BOTH, expand=True)
        
        def update_preview():
            first_idx = first_combo.current()
            second_idx = second_combo.current()
            
            if first_idx >= 0 and second_idx >= 0 and first_idx != second_idx:
                first_pdf = self.pdf_list[first_idx]
                second_pdf = self.pdf_list[second_idx]
                
                try:
                    first_doc = self.pdf_documents.get(first_pdf) or fitz.open(first_pdf)
                    second_doc = self.pdf_documents.get(second_pdf) or fitz.open(second_pdf)
                    
                    preview_text.config(state=tk.NORMAL)
                    preview_text.delete(1.0, tk.END)
                    preview_text.insert(tk.END, f"Merged PDF will contain:\n\n")
                    preview_text.insert(tk.END, f"📄 {os.path.basename(first_pdf)} ({len(first_doc)} pages)\n")
                    preview_text.insert(tk.END, f"📄 {os.path.basename(second_pdf)} ({len(second_doc)} pages)\n\n")
                    preview_text.insert(tk.END, f"Total pages: {len(first_doc) + len(second_doc)}")
                    preview_text.config(state=tk.DISABLED)
                    
                except Exception as e:
                    preview_text.config(state=tk.NORMAL)
                    preview_text.delete(1.0, tk.END)
                    preview_text.insert(tk.END, f"Error reading PDF info: {str(e)}")
                    preview_text.config(state=tk.DISABLED)
        
        first_combo.bind('<<ComboboxSelected>>', lambda e: update_preview())
        second_combo.bind('<<ComboboxSelected>>', lambda e: update_preview())
        
        # Buttons
        button_frame = ttk.Frame(main_frame)
        button_frame.pack(fill=tk.X, pady=10)
        
        def on_merge():
            first_idx = first_combo.current()
            second_idx = second_combo.current()
            
            if first_idx < 0 or second_idx < 0:
                messagebox.showwarning("Warning", "Please select both PDFs to merge.")
                return
                
            if first_idx == second_idx:
                messagebox.showwarning("Warning", "Please select two different PDFs.")
                return
                
            dialog.destroy()
            self.perform_merge(self.pdf_list[first_idx], self.pdf_list[second_idx])
        
        ttk.Button(button_frame, text="Cancel", command=dialog.destroy).pack(side=tk.RIGHT, padx=(10, 0))
        ttk.Button(button_frame, text="Merge PDFs", command=on_merge, style='Accent.TButton').pack(side=tk.RIGHT)
        
        # Update preview initially
        self.root.after(100, update_preview)
        
    def show_external_merge_dialog(self, external_path):
        """Show dialog to choose merge order with external PDF"""
        dialog = tk.Toplevel(self.root)
        dialog.title("Merge with External PDF")
        dialog.geometry("500x300")
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Center dialog
        dialog.geometry("+%d+%d" % (self.root.winfo_rootx() + 150, self.root.winfo_rooty() + 150))
        
        main_frame = ttk.Frame(dialog)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=20)
        
        ttk.Label(main_frame, text="Choose Merge Order", font=('Segoe UI', 12, 'bold')).pack(pady=(0, 10))
        
        # Current PDF info
        current_frame = ttk.LabelFrame(main_frame, text="Current PDF", padding=10)
        current_frame.pack(fill=tk.X, pady=5)
        
        current_name = os.path.basename(self.pdf_path) if self.pdf_path else "Current Document"
        current_pages = len(self.pdf_document) if self.pdf_document else 0
        ttk.Label(current_frame, text=f"📄 {current_name} ({current_pages} pages)").pack(anchor=tk.W)
        
        # External PDF info
        external_frame = ttk.LabelFrame(main_frame, text="External PDF", padding=10)
        external_frame.pack(fill=tk.X, pady=5)
        
        external_name = os.path.basename(external_path)
        try:
            external_doc = fitz.open(external_path)
            external_pages = len(external_doc)
            external_doc.close()
        except:
            external_pages = "?"
        
        ttk.Label(external_frame, text=f"📄 {external_name} ({external_pages} pages)").pack(anchor=tk.W)
        
        # Order selection
        order_frame = ttk.LabelFrame(main_frame, text="Merge Order", padding=10)
        order_frame.pack(fill=tk.X, pady=10)
        
        order_var = tk.StringVar(value="current_first")
        
        ttk.Radiobutton(order_frame, text=f"Current PDF first, then {external_name}", 
                       variable=order_var, value="current_first").pack(anchor=tk.W, pady=2)
        ttk.Radiobutton(order_frame, text=f"{external_name} first, then Current PDF", 
                       variable=order_var, value="external_first").pack(anchor=tk.W, pady=2)
        
        # Buttons
        button_frame = ttk.Frame(main_frame)
        button_frame.pack(fill=tk.X, pady=10)
        
        def on_merge():
            if order_var.get() == "current_first":
                first_path = self.pdf_path
                second_path = external_path
            else:
                first_path = external_path
                second_path = self.pdf_path
                
            dialog.destroy()
            self.perform_merge(first_path, second_path)
        
        ttk.Button(button_frame, text="Cancel", command=dialog.destroy).pack(side=tk.RIGHT, padx=(10, 0))
        ttk.Button(button_frame, text="Merge PDFs", command=on_merge, style='Accent.TButton').pack(side=tk.RIGHT)
        
    def perform_merge(self, first_pdf_path, second_pdf_path):
        """Perform the actual PDF merge operation"""
        try:
            self.status_var.set("Merging PDFs...")
            
            # Get actual PDF paths (use modified versions if they exist)
            actual_first_path = self.get_actual_pdf_path(first_pdf_path)
            actual_second_path = self.get_actual_pdf_path(second_pdf_path)
            
            # Store the first PDF name for default naming (use original path for naming)
            self.merged_first_pdf_name = Path(first_pdf_path).stem
            print(f"DEBUG: Stored merged PDF name: '{self.merged_first_pdf_name}' from path: '{first_pdf_path}'")
            print(f"DEBUG: Using actual paths - First: '{actual_first_path}', Second: '{actual_second_path}'")
            
            # Create temporary file for merged PDF
            import tempfile
            temp_dir = tempfile.gettempdir()
            temp_filename = f"merged_pdf_{int(time.time())}.pdf"
            self.merged_temp_path = os.path.join(temp_dir, temp_filename)
            
            # Open both PDFs using actual paths (modified or original)
            first_doc = fitz.open(actual_first_path)
            second_doc = fitz.open(actual_second_path)
            
            # Create new merged document
            merged_doc = fitz.open()  # Create empty document
            
            # Add all pages from first PDF
            merged_doc.insert_pdf(first_doc)
            
            # Add all pages from second PDF
            merged_doc.insert_pdf(second_doc)
            
            # Save merged PDF to temporary file
            merged_doc.save(self.merged_temp_path)
            
            # Close documents
            first_doc.close()
            second_doc.close()
            merged_doc.close()
            
            # Load the merged PDF for editing
            self.load_merged_pdf()
            
            self.status_var.set(f"PDFs merged successfully - {len(self.pdf_document)} pages total")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to merge PDFs:\n{str(e)}")
            self.status_var.set("Error merging PDFs")
            
    def load_merged_pdf(self):
        """Load the merged PDF and enable edit mode"""
        try:
            # Preserve the first PDF name before clearing state
            preserved_first_pdf_name = self.merged_first_pdf_name
            
            # Clear existing state
            self.clear_all_state()
            
            # Set merged PDF flags
            self.is_merged_pdf = True
            self.merged_first_pdf_name = preserved_first_pdf_name  # Restore the preserved name
            self.pdf_path = self.merged_temp_path
            
            # Load the merged document
            self.pdf_document = fitz.open(self.merged_temp_path)
            
            if len(self.pdf_document) == 0:
                messagebox.showerror("Error", "Merged PDF appears to be empty.")
                return
                
            # Update UI
            self.update_file_label()
            
            # Initialize for editing
            self.initialize_edit_session()
            
            # Enable edit mode automatically
            self.edit_mode_var.set(True)
            self.toggle_edit_mode()
            
            # Show the save merged button
            self.update_merge_ui()
            
            # Generate thumbnails
            self.status_var.set("Generating thumbnails for merged PDF...")
            threading.Thread(target=self.generate_thumbnails, daemon=True).start()
            
            # Show success message
            messagebox.showinfo("Success", 
                              f"PDFs merged successfully!\n\n"
                              f"Total pages: {len(self.pdf_document)}\n"
                              f"Edit mode enabled - you can reorder, delete, and rotate pages.\n"
                              f"Use 'Save Merged PDF' when ready to save the final result.")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load merged PDF:\n{str(e)}")
            
    def clear_all_state(self):
        """Clear all application state before loading new PDF"""
        # Clear thumbnails
        if hasattr(self, 'page_thumbnails'):
            self.page_thumbnails.clear()
        
        # Clear widgets
        if hasattr(self, 'page_widgets'):
            self.page_widgets.clear()
            
        # Clear selections
        if hasattr(self, 'selected_ranges'):
            self.selected_ranges.clear()
            
        # Clear crops
        if hasattr(self, 'crop_rectangles'):
            self.crop_rectangles.clear()
            self.crop_thumbnails.clear()
            
        # Reset edit state
        self.has_edited = False
        self.deleted_pages.clear() if hasattr(self, 'deleted_pages') else None
        self.page_rotations.clear() if hasattr(self, 'page_rotations') else None
        
        # Clear current selection
        self.current_selection = {'start': None, 'end': None}
        
        # Disable modes
        self.edit_mode = False
        self.crop_mode = False
        if hasattr(self, 'edit_mode_var'):
            self.edit_mode_var.set(False)
        if hasattr(self, 'crop_mode_var'):
            self.crop_mode_var.set(False)
            
        # Reset merge state
        self.is_merged_pdf = False
        self.merged_first_pdf_name = None
            
        # Clear thumbnails frame
        if hasattr(self, 'thumbnails_frame'):
            for widget in self.thumbnails_frame.winfo_children():
                widget.destroy()

    def update_merge_ui(self):
        """Update UI elements related to merge functionality"""
        if hasattr(self, 'save_merged_btn'):
            if self.is_merged_pdf:
                self.save_merged_btn.pack(side=tk.LEFT, padx=(2, 0))
            else:
                self.save_merged_btn.pack_forget()

    def save_merged_pdf(self):
        """Save the merged and edited PDF"""
        if not self.is_merged_pdf or not self.pdf_document:
            messagebox.showwarning("Warning", "No merged PDF to save.")
            return
            
        # Get save location with smart default naming
        if self.merged_first_pdf_name:
            default_name = f"{self.merged_first_pdf_name}_merged.pdf"
            print(f"DEBUG: Using merged name '{self.merged_first_pdf_name}' -> default: '{default_name}'")
        else:
            default_name = "merged_document.pdf"
            print(f"DEBUG: No merged name stored, using fallback: '{default_name}'")
            
        save_path = filedialog.asksaveasfilename(
            title="Save Merged PDF",
            defaultextension=".pdf",
            initialfile=default_name,
            filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")]
        )
        
        if not save_path:
            return
            
        try:
            self.status_var.set("Saving merged PDF...")
            
            # Create final PDF with all edits applied
            merged_writer = PyPDF2.PdfWriter()
            merged_reader = PyPDF2.PdfReader(self.merged_temp_path)
            
            # Apply page order, deletions, and rotations
            for page_index in self.page_order:
                if page_index in self.deleted_pages:
                    continue
                    
                if page_index < len(merged_reader.pages):
                    page = merged_reader.pages[page_index]
                    
                    # Apply rotation if set for this page (1-based)
                    page_number_1based = page_index + 1
                    if page_number_1based in self.page_rotations:
                        rotation_angle = self.page_rotations[page_number_1based]
                        if rotation_angle == 90:
                            page = page.rotate(90)
                        elif rotation_angle == 180:
                            page = page.rotate(180)
                        elif rotation_angle == 270:
                            page = page.rotate(270)
                    
                    merged_writer.add_page(page)
            
            # Write final PDF
            with open(save_path, 'wb') as output_file:
                merged_writer.write(output_file)
            
            # Show success message
            details = []
            if self.has_edited:
                details.append("reordered pages")
            if self.deleted_pages:
                details.append(f"removed {len(self.deleted_pages)} pages")
            if self.page_rotations:
                details.append(f"applied {len(self.page_rotations)} rotations")
                
            detail_text = f" ({', '.join(details)})" if details else ""
            
            messagebox.showinfo("Success", 
                              f"Merged PDF saved successfully!\n\n"
                              f"File: {os.path.basename(save_path)}\n"
                              f"Pages: {len(merged_writer.pages)}{detail_text}")
                              
            self.status_var.set(f"Merged PDF saved: {os.path.basename(save_path)}")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to save merged PDF:\n{str(e)}")
            self.status_var.set("Error saving merged PDF")

def main():
    """Main application entry point"""
    root = tk.Tk()
    
    # Set window icon if available (you can add an icon file)
    try:
        # root.iconbitmap('pdf_icon.ico')  # Add this if you have an icon
        pass
    except:
        pass
    
    # Center window on screen
    root.eval('tk::PlaceWindow . center')
    
    app = VisualPDFSplitterApp(root)
    
    # Handle window closing - no confirmation needed
    def on_closing():
        root.destroy()
    
    root.protocol("WM_DELETE_WINDOW", on_closing)
    
    try:
        root.mainloop()
    except KeyboardInterrupt:
        pass

if __name__ == "__main__":
    main()