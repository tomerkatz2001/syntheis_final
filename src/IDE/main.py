import sys
from PyQt5.QtWidgets import QApplication, QMainWindow, QTextEdit, QAction, QFileDialog, QTextBrowser, QWidget, \
    QVBoxLayout, QHBoxLayout, QTableWidget, QPushButton, QLabel, QSizePolicy, QScrollArea, QMessageBox
from PyQt5.QtGui import QFontDatabase, QTextCursor, QFont
from PyQt5.QtCore import Qt, QTimer
from while_lang.wp import getVars, synthesize


class CodeEditor(QMainWindow):
    def __init__(self):
        super().__init__()

        self.init_ui()

    def init_ui(self):
        # Create a widget to hold line numbers, text edit, and table
        self.central_widget = QWidget(self)
        self.setCentralWidget(self.central_widget)

        self.layout = QHBoxLayout(self.central_widget)
        font = QFontDatabase.systemFont(QFontDatabase.FixedFont)
        # Line number area
        self.line_number_area = LineNumberArea(self)

        # Text edit
        self.text_edit = QTextEdit(self)
        self.text_edit.cursorPositionChanged.connect(self.update_line_number_area)

        self.error_message = QLabel()
        self.error_message.setStyleSheet("color: red;")
        self.error_message.setVisible(False)

        # Table widget
        self.buildTable()
        self.scroll_area.hide()

        # Button to toggle table visibility
        self.show_table_button = QPushButton("Synthesize!")
        self.show_table_button.setStyleSheet(
            "QPushButton { background-color: #4CAF50; color: white; border: none; padding: 8px 16px; border-radius: 5px; font-weight: bold; }"
            "QPushButton:hover { background-color: #45a049; }"
            "QPushButton:pressed { background-color: #3e854e; }"
        )
        self.show_table_button.clicked.connect(self.toggle_table)



        # Load a monospace font for code

        self.text_edit.setFont(font)

        # Set stylesheet for dark mode appearance
        stylesheet = """
            QTextEdit {
                background-color: #282C34;
                color: #ABB2BF;
                border: none;
                selection-background-color: #3E4451;
                selection-color: white;
            }
            QMainWindow {
                background-color: #282C34;
            }
            QMenuBar {
                background-color: #282C34;
                color: #ABB2BF;
            }
            QMenuBar::item:selected {
                background-color: #3E4451;
            }
            QMenu {
                background-color: #282C34;
                color: #ABB2BF;
            }
            QMenu::item:selected {
                background-color: #3E4451;
            }
        """
        self.setStyleSheet(stylesheet)

        # Create a File menu
        self.file_menu = self.menuBar().addMenu('File')

        #add menu for beauty
        self.menuBar().addMenu('Edit').addAction(QAction("how uses this?", self))
        self.menuBar().addMenu('View').addAction(QAction("do you really think we implemented this?", self))
        self.menuBar().addMenu('Navigation').addAction(QAction("TODO", self))
        self.menuBar().addMenu('Code').addAction(QAction("code", self))
        self.menuBar().addMenu('Tools').addAction(QAction("hammer", self))


        # Create actions for opening and saving files
        self.open_action = QAction('Open', self)
        self.open_action.triggered.connect(self.open_file)
        self.file_menu.addAction(self.open_action)

        self.save_action = QAction('Save', self)
        self.save_action.triggered.connect(self.save_file)
        self.file_menu.addAction(self.save_action)

        self.layout.addWidget(self.line_number_area)
        self.layout.addWidget(self.text_edit)
        self.layout.addWidget(self.scroll_area)
        self.layout.addWidget(self.show_table_button)
        self.layout.addWidget(self.error_message)
        self.setGeometry(100, 100, 800, 600)
        self.setWindowTitle('The whileLang official Code Editor')

    def open_file(self):
        options = QFileDialog.Options()
        options |= QFileDialog.ReadOnly
        file_name, _ = QFileDialog.getOpenFileName(self, "Open File", "", "All Files (*)", options=options)

        if file_name:
            with open(file_name, 'r') as file:
                self.text_edit.setPlainText(file.read())

    def save_file(self):
        options = QFileDialog.Options()
        file_name, _ = QFileDialog.getSaveFileName(self, "Save File", "", "All Files (*)", options=options)

        if file_name:
            with open(file_name, 'w') as file:
                file.write(self.text_edit.toPlainText())

    def update_line_number_area(self):
        contents = self.text_edit.toPlainText()
        num_lines = contents.count('\n') + 1
        self.line_number_area.set_number_of_lines(num_lines)

    def toggle_table(self):
        if self.scroll_area.isVisible():
            code_base = self.text_edit.toPlainText()
            inputs, outputs = self.table_widget.collect_table_values()
            result = synthesize(code_base, inputs, outputs )
            self.text_edit.setPlainText(result)
            self.scroll_area.hide()
        else:
            try:
                programs_vars = getVars(self.text_edit.toPlainText())
            except:
                self.show_error_message("There is somthing wrong with the program. fix it first")
                return
            self.buildTable(varNames=programs_vars)
            self.scroll_area.show()


    def show_error_message(self, message):
        self.error_message.setText(message)
        self.error_message.setVisible(True)
        self.error_timer = QTimer(self)
        self.error_timer.timeout.connect(self.hide_error_message)
        self.error_timer.start(3000)

    def hide_error_message(self):
        self.error_message.setVisible(False)
        self.error_timer.stop()

    def buildTable(self, varNames=['x']):
        self.table_widget = CustomTableWidget(varNames)
        self.scroll_area = QScrollArea()
        self.scroll_area.setWidget(self.table_widget)
        self.scroll_area.setWidgetResizable(True)  # Allow resizing of the contained widget
        self.scroll_area.setContentsMargins(0, 0, 0, 0)  # Remove any spacing around the table
        self.scroll_area.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Expanding)  # Fixed width, resizable height
        self.scroll_area.setFixedWidth(316)  # Set a maximum width
        self.scroll_area.setMaximumHeight((len(varNames) + 1) * 45)  # Set a maximum width
        self.scroll_area.setStyleSheet("background: transparent; border: none;")
        self.scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)  # Disable horizontal scrolling
        self.scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOff)  # Disable horizontal scrolling




class LineNumberArea(QWidget):
    def __init__(self, editor):
        super().__init__(editor)
        self.editor = editor
        self.setFixedWidth(50)

        self.layout = QVBoxLayout(self)
        self.layout.setAlignment(Qt.AlignTop)

        # Create a QLabel for line numbers
        self.line_numbers = QLabel(self)
        self.line_numbers.setAlignment(Qt.AlignRight)
        self.layout.addWidget(self.line_numbers)

        self.setStyleSheet("QLabel { background-color: #2E313A; color: #ABB2BF; border: none; }")

    def set_number_of_lines(self, num_lines):
        line_numbers_text = '\n'.join(str(i) for i in range(1, num_lines + 1))
        self.line_numbers.setText(line_numbers_text)
        # Load a monospace font for code
        font = QFontDatabase.systemFont(QFontDatabase.FixedFont)
        self.line_numbers.setFont(font)

class CustomTableWidget(QTableWidget):
    def __init__(self, row_headers):
        super().__init__(len(row_headers), 2)  # Two columns for "INPUT" and "OUTPUT"
        self._values = {r: {0:{}, 1:{}} for r in range(len(row_headers))}
        # Set size policy to minimum
        self.setSizePolicy(QSizePolicy.Minimum, QSizePolicy.Minimum)
        # Set background color and border style for the table
        self.setStyleSheet(
            "QTableWidget { background-color: #1E1E1E; border: 1px solid white; color: white; }"
            "QTableWidget::item { background-color: transparent; border: 1px solid white; padding: 5px; }"
        )

        # Set font
        font = QFont("Courier New", 10)
        self.setFont(font)

        # Customize header appearance
        header_style = (
            "QHeaderView::section { background-color: #2E313A; color: white; border-bottom: 2px solid white; padding: 5px; }"
            "QHeaderView::section:vertical { border-right: 2px solid white; }"
        )
        self.horizontalHeader().setStyleSheet(header_style)
        self.verticalHeader().setStyleSheet(header_style)

        self.verticalHeader().setDefaultSectionSize(20)  # Adjust row height

        # Set row headers
        self.setVerticalHeaderLabels(row_headers)

        # Set column headers
        self.setHorizontalHeaderLabels(["INPUT VALUE", "OUTPUT VALUE"])

        # Resize rows and columns to contents
        self.resizeRowsToContents()
        self.resizeColumnsToContents()

        self.itemChanged.connect(self.log_change)

    def log_change(self, item):
        row = item.row()
        col = item.column()
        self._values[row].update({col: item.text()})


    def collect_table_values(self):
        input_values = {}
        output_values = {}

        for row in range(self.rowCount()):
            row_header = self.verticalHeaderItem(row).text()

            input_value = self._values[row][0]
            output_value = self._values[row][1]
            if input_value and output_value:
                input_values[row_header] = input_value
                output_values[row_header] = output_value

        return input_values, output_values

if __name__ == '__main__':
    app = QApplication(sys.argv)
    app.setStyle('Fusion')  # Set Fusion style for consistent look across platforms
    app.setAttribute(Qt.AA_UseHighDpiPixmaps)
    editor = CodeEditor()
    editor.show()
    sys.exit(app.exec_())
