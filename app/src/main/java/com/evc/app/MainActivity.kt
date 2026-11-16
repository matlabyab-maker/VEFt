package com.evc.app

import android.app.Activity
import android.app.AlertDialog
import android.content.Intent
import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.graphics.Rect
import android.graphics.Color
import android.graphics.drawable.GradientDrawable
import android.content.ContentValues
import android.os.Environment
import android.provider.MediaStore
import android.provider.OpenableColumns
import android.media.MediaMetadataRetriever
import android.media.MediaPlayer
import android.graphics.SurfaceTexture
import android.view.TextureView
import android.view.Surface
import android.media.MediaExtractor
import android.media.MediaFormat
import android.media.MediaMuxer
import android.media.MediaCodec
import android.net.Uri
import android.os.Bundle
import android.os.Handler
import android.os.SystemClock
import android.os.Looper
import android.view.Gravity
import android.view.View
import android.view.ViewGroup
import android.view.MotionEvent
import android.graphics.Canvas
import android.graphics.Paint
import android.graphics.Typeface
import android.graphics.RectF
import android.widget.Button
import android.widget.CheckBox
import android.widget.PopupWindow
import android.widget.EditText
import android.widget.FrameLayout
import android.widget.GridLayout
import android.widget.HorizontalScrollView
import android.widget.ImageView
import android.widget.LinearLayout
import android.widget.MediaController
import android.widget.ScrollView
import android.widget.SeekBar
import android.widget.TextView
import android.text.Spannable
import android.text.SpannableString
import android.text.style.ForegroundColorSpan
import android.text.style.StyleSpan
import android.text.TextWatcher
import android.text.StaticLayout
import android.text.Layout
import android.text.TextPaint
import android.text.Editable
import android.widget.Toast
import android.widget.VideoView
import androidx.media3.common.MediaItem
import androidx.media3.transformer.Effects
import androidx.media3.transformer.EditedMediaItem
import androidx.media3.transformer.EditedMediaItemSequence
import androidx.media3.transformer.DefaultEncoderFactory
import androidx.media3.transformer.VideoEncoderSettings
import androidx.media3.transformer.Transformer
import androidx.media3.transformer.Composition
import androidx.media3.transformer.ExportResult
import androidx.media3.transformer.ExportException
import androidx.media3.effect.RgbAdjustment
import androidx.media3.effect.HslAdjustment
import androidx.media3.effect.Crop
import androidx.media3.effect.OverlayEffect
import androidx.media3.effect.StaticOverlaySettings
import androidx.media3.effect.TextOverlay
import com.arthenica.ffmpegkit.FFmpegKit
import com.arthenica.ffmpegkit.ReturnCode
import java.util.concurrent.Executors
import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import kotlin.math.max
import kotlin.math.abs

enum class TrackClipKind { AUDIO, SUBTITLE, VIDEO }

data class TrackClip(
    val id: Long,
    val uri: Uri,
    val kind: TrackClipKind,
    val name: String,
    val startMs: Long,
    val sourceStartMs: Long,
    val durationMs: Long,
    val sourceDurationMs: Long
)

class MainActivity : Activity() {
    private lateinit var videoView: VideoView
    private lateinit var placementOverlay: PlacementOverlayView
    private var placementMode: PlacementOverlayView.Mode = PlacementOverlayView.Mode.NONE
    private lateinit var playerColorPreview: ImageView
    private val previewBitmaps = mutableMapOf<Int, Bitmap>()
    private var playerPreviewRequest = 0
    private lateinit var statusText: TextView
    private lateinit var emptyHint: TextView
    private lateinit var storyboardRows: LinearLayout
    private lateinit var selectionText: TextView
    private lateinit var timeModeButton: Button
    private var storyboardScaleDetector: android.view.ScaleGestureDetector? = null
    private var pendingStoryboardColumns: Int? = null
    private lateinit var timelineView: TimelineView
    private val timelineSplitPoints = sortedSetOf<Long>()
    private val deletedTimelineRanges = mutableListOf<Pair<Long, Long>>()
    private var selectedTimelineRange: Pair<Long, Long>? = null
    private val mainHandler = Handler(Looper.getMainLooper())
    private var suppressStoryboardAutoApply = false
    private val storyboardAutoApplyRunnable = Runnable {
        if (!suppressStoryboardAutoApply && selectedUri != null) applyStoryboardTimeRange()
    }
    private val worker = Executors.newSingleThreadExecutor()
    // Decode storyboard thumbnails in a small pool; one MediaMetadataRetriever per worker.
    // This avoids serial decoding becoming a long bottleneck for the first rows.
    private val storyboardFrameWorkers = Executors.newFixedThreadPool(2)
    // Keep timeline sampling independent so storyboard frames and the timeline do not share a decoder.
    private val timelineThumbnailWorker = Executors.newSingleThreadExecutor()
    private val selectedFrames = linkedSetOf<Int>()
    // Anchor used for tap-then-long-press range toggling in the storyboard.
    private var storyboardRangeAnchorIndex: Int? = null
    private val frameViews = mutableMapOf<Int, FrameLayout>()
    private val frameBitmaps = mutableMapOf<Int, Bitmap>()
    // When cover mode is enabled, a storyboard tap chooses the exported video's poster frame.
    private var storyboardCoverMode = false
    private var selectedCoverFrameIndex: Int? = null
    @Volatile private var storyboardPriorityIndex: Int = 0
    private var allViewMode = false
    private var storyboardNavigationMode = 1
    private var userStoryboardColumns: Int? = null
    // Exact timestamps for storyboard cells populated by image-based scene search.
    private val imageSearchFrameTimes = mutableMapOf<Int, Long>()
    private val deletedStoryboardFrames = linkedSetOf<Int>()
    private var selectedUri: Uri? = null
    private var activeTransformer: Transformer? = null
    private var videoDurationMs = 0L
    private var manualOutputNameEnabled = false
    private var playbackFrameIndex = -1
    private var storyboardStartMs = 0L
    private var storyboardEndMs = 0L
    private var storyboardIntervalMs: Long? = null
    // The normal storyboard uses 120 cells; extra cells exist only for a custom interval/range.
    private var activeStoryboardFrameCount = DEFAULT_STORYBOARD_FRAME_COUNT
    private var storyboardGeneration = 0
    private data class RgbProfile(val red: Float, val green: Float, val blue: Float, val saturation: Float)
    private val frameColorProfiles = mutableMapOf<Int, RgbProfile>()
    // Best-effort, luminance-guided colorization for black-and-white footage.
    private var autoColorEnabled = false
    private val mergeUris = mutableListOf<Uri>()
    private val importedVideoUris = mutableListOf<Uri>()
    private var allViewPreviousColorVisibility = View.GONE
    private val PICK_MERGE_VIDEOS = 7304
    private val PICK_REFERENCE_IMAGE = 7305
    private val PICK_VECTOR_VIDEOS = 7306
    private val PICK_EXTERNAL_AUDIO = 7307
    private val PICK_EXTERNAL_SUBTITLE = 7308
    private val PICK_OVERLAY_VIDEO = 7309
    private val PICK_APPEND_VIDEOS = 7310
    private val PICK_TRACK_VIDEO = 7311
    private var overlayVideoUri: Uri? = null
    private lateinit var overlayVideoLayer: FrameLayout
    private lateinit var overlayPreviewTexture: TextureView
    private var overlayPreviewPlayer: MediaPlayer? = null
    private var overlayPreviewSurface: Surface? = null
    private var overlayPreviewVideoWidth = 16
    private var overlayPreviewVideoHeight = 9
    private var overlayVideoXPercent = 70
    private var overlayVideoYPercent = 5
    private var overlayVideoWidthPercent = 25
    private var textXPercent = 5
    private var textYPercent = 5
    private var liveTextSize = 36
    private var externalAudioUri: Uri? = null
    private var externalSubtitleUri: Uri? = null
    private val trackClips = mutableListOf<TrackClip>()
    private var nextTrackClipId = 1L
    private lateinit var trackTimelineView: TrackTimelineView
    private var selectedTrackClipId: Long? = null
    private val vectorUris = mutableListOf<Uri>()
    private var referenceImageUri: Uri? = null
    // Crop margins are stored as percentages of the source frame and reused for export.
    private var cropLeftPct = 0
    private var cropTopPct = 0
    private var cropRightPct = 0
    private var cropBottomPct = 0
    private var cropSettingsSaved = false
    private lateinit var cropOverlay: FreeCropOverlayView
    private lateinit var freeCropControls: LinearLayout
    private var freeCropMode = false
    private var autoCropMode = false
    private data class EditorHistoryState(val splitPoints: List<Long>, val deletedRanges: List<Pair<Long, Long>>, val clips: List<TrackClip>, val profiles: Map<Int, RgbProfile>, val crop: List<Int>, val cropSaved: Boolean, val autoColor: Boolean, val overlayUri: Uri?, val text: String, val textX: Int, val textY: Int, val textSize: Int, val overlayX: Int, val overlayY: Int, val overlayWidth: Int, val merge: List<Uri>, val vector: List<Uri>, val reference: Uri?)
    private val undoHistory = java.util.ArrayDeque<EditorHistoryState>()
    private val redoHistory = java.util.ArrayDeque<EditorHistoryState>()
    private var restoringHistory = false
    private val maxHistorySteps = 200
    private val playbackSyncRunnable = object : Runnable {
        override fun run() {
            if (!::videoView.isInitialized || !::timelineView.isInitialized) return
            val position = try { videoView.currentPosition.toLong() } catch (_: Exception) { timelineView.playheadMs }
            timelineView.setPlayhead(position)
            updateStoryboardPlaybackHighlight(position)
            if (::overlayVideoLayer.isInitialized) updateOverlayVideoVisibility(position)
            // Keep polling while paused too: playback may be started from the MediaController.
            mainHandler.postDelayed(this, 40L)
        }
    }

    // Applies to original-quality stream-copy exports (main export, timeline, storyboard segments).
    private var outputContainerMatroska = false

    /**
     * Project-wide control rule: every button uses the 52dp height of "لغو انتخاب".
     * Toolbar actions follow the same height so their labels remain inside the horizontal rail.
     * Labels are wrapped and measured to use the largest size that fits without clipping.
     * A root layout listener also catches controls added later inside editor windows.
     */
    private fun installProjectButtonAndLabelRules() {
        val root = findViewById<ViewGroup>(R.id.mainRootLayout) ?: return
        root.viewTreeObserver.addOnGlobalLayoutListener {
            if (root.isAttachedToWindow) standardizeControlTree(root)
        }
    }

    private fun standardizeControlTree(view: View) {
        val standardHeight = (52f * resources.displayMetrics.density + 0.5f).toInt()
        if (view is CheckBox) {
            fitProjectLabel(view, isCheckable = true)
        } else if (view is Button) {
            if (view.id != R.id.openButton && view.id != R.id.outputChangesButton) {
                val lp = view.layoutParams
                if (lp != null && lp.height != standardHeight) {
                    lp.height = standardHeight
                    view.layoutParams = lp
                }
            }
            fitProjectLabel(view, isCheckable = false)
        }
        if (view is ViewGroup) {
            for (index in 0 until view.childCount) standardizeControlTree(view.getChildAt(index))
        }
    }

    private fun standardizeDialogButtons(dialog: AlertDialog) {
        val standardHeight = (52f * resources.displayMetrics.density + 0.5f).toInt()
        listOf(AlertDialog.BUTTON_POSITIVE, AlertDialog.BUTTON_NEGATIVE, AlertDialog.BUTTON_NEUTRAL).forEach { which ->
            dialog.getButton(which)?.let { button ->
                button.post {
                    val lp = button.layoutParams
                    if (lp != null) {
                        lp.height = standardHeight
                        button.layoutParams = lp
                    }
                    fitProjectLabel(button, isCheckable = false)
                }
            }
        }
    }

    private fun fitProjectLabel(view: TextView, isCheckable: Boolean) {
        val label = view.text ?: return
        if (label.isEmpty() || view.width <= 0 || view.height <= 0) return

        // Keep labels centered, permit deliberate multi-line wrapping, and never ellipsize.
        if (view.isSingleLine) view.setSingleLine(false)
        if (view.maxLines != 100) view.maxLines = 100
        if (view.ellipsize != null) view.ellipsize = null
        if (view.gravity != Gravity.CENTER) view.gravity = Gravity.CENTER
        if (view.includeFontPadding) view.includeFontPadding = false

        val availableWidth = (view.width - view.compoundPaddingLeft - view.compoundPaddingRight)
            .coerceAtLeast((24f * resources.displayMetrics.density).toInt())
        val availableHeight = (view.height - view.compoundPaddingTop - view.compoundPaddingBottom)
            .coerceAtLeast((18f * resources.displayMetrics.density).toInt())
        val basePaint = TextPaint(view.paint)
        val density = resources.displayMetrics.scaledDensity
        val minSp = 5.5f
        val maxSp = 22f
        val words = label.toString().trim().split(Regex("\\s+")).filter { it.isNotEmpty() }
        var chosenSp = minSp
        var size = maxSp
        while (size >= minSp) {
            basePaint.textSize = size * density
            // Never split a word across lines: reduce the font until even the longest
            // complete word fits the available width, then wrap only at whitespace.
            val everyWordFits = words.all { basePaint.measureText(it) <= availableWidth }
            if (everyWordFits) {
                val layout = StaticLayout.Builder.obtain(label, 0, label.length, basePaint, availableWidth)
                    .setAlignment(Layout.Alignment.ALIGN_CENTER)
                    .setIncludePad(false)
                    .setMaxLines(100)
                    .setBreakStrategy(Layout.BREAK_STRATEGY_SIMPLE)
                    .setHyphenationFrequency(Layout.HYPHENATION_FREQUENCY_NONE)
                    .build()
                if (layout.lineCount <= 100 && layout.height <= availableHeight) {
                    chosenSp = size
                    break
                }
            }
            size -= 0.5f
        }
        val chosenPx = chosenSp * density
        if (kotlin.math.abs(view.textSize - chosenPx) > 0.25f) {
            view.setTextSize(android.util.TypedValue.COMPLEX_UNIT_SP, chosenSp)
        }
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContentView(R.layout.activity_main)
        installProjectButtonAndLabelRules()
        installStoryboardAutoApply()
        // Collapsible editor windows must always start closed. Do not let a restored
        // view state or a video-import/layout refresh expose a panel without a tap.
        intArrayOf(
            R.id.timelinePanel,
            R.id.trackPanel,
            R.id.timelineActionButtons,
            R.id.storyboardTimeRangeRow,
            R.id.fixedColorControls,
            R.id.freeCropControls,
            R.id.textOverlayPanel,
            R.id.overlayVideoPanel
        ).forEach { findViewById<View>(it)?.visibility = View.GONE }
        ensureSingleUndoRedoButtons()
        setupDraggableToolbarRail()
        findViewById<View>(R.id.mainRootLayout).setOnDragListener { _, event ->
            if (event.action == android.view.DragEvent.ACTION_DROP) {
                val frameIndex = event.localState as? Int
                if (frameIndex != null) {
                    seekToStoryboardFrame(frameIndex)
                    selectedFrames.clear(); selectedFrames.add(frameIndex)
                    updateSelectionText(); refreshSelectionStyles()
                    statusText.text = "فریم ${frameIndex + 1} در بخش ویرایش انتخاب شد؛ اکنون ابزار موردنظر را اجرا کنید"
                    true
                } else false
            } else event.action == android.view.DragEvent.ACTION_DRAG_STARTED
        }
        findViewById<Button>(R.id.outputChangesButton).setOnClickListener { exportCombinedChanges() }
        findViewById<Button>(R.id.globalDeleteButton).setOnClickListener { recordUndoState(); deleteSelectionOrShowOptions() }
        findViewById<Button>(R.id.undoButton).setOnClickListener { undoEditorStep() }
        findViewById<Button>(R.id.redoButton).setOnClickListener { redoEditorStep() }
        findViewById<Button>(R.id.saveEditButton).setOnClickListener { saveActiveEdit() }
        findViewById<Button>(R.id.cancelEditButton).setOnClickListener { cancelActiveEdit() }
        val fixedColorControls = findViewById<View>(R.id.fixedColorControls)
        fixedColorControls.visibility = View.GONE
        findViewById<Button>(R.id.colorPanelButton).setOnClickListener {
            if (fixedColorControls.visibility != View.VISIBLE) recordUndoState()
            fixedColorControls.visibility = if (fixedColorControls.visibility == View.VISIBLE) View.GONE else View.VISIBLE
            if (fixedColorControls.visibility == View.VISIBLE) statusText.text = "پنجرهٔ رنگ‌آمیزی باز شد؛ پس از تنظیم، دکمهٔ پایان را بزنید"
        }
        findViewById<Button>(R.id.finishColorPanelButton).setOnClickListener {
            fixedColorControls.visibility = View.GONE
            statusText.text = "تنظیمات رنگ حفظ شد؛ برای ویرایش دوباره دکمهٔ «رنگ‌آمیزی» را بزنید"
        }
        findViewById<Button>(R.id.autoColorButton).setOnClickListener {
            recordUndoState()
            autoColorEnabled = !autoColorEnabled
            findViewById<Button>(R.id.autoColorButton).text = if (autoColorEnabled) "Auto Color: روشن" else "Auto Color"
            statusText.post {
                statusText.text = if (autoColorEnabled)
                    "Auto Color روشن شد؛ رنگ‌آمیزی تقریبی بر اساس روشنایی تصویر در «خروجی تغییرات» اعمال می‌شود. تشخیص معنایی آسمان/درخت/صورت با مدل هوش مصنوعی انجام نمی‌شود."
                else "Auto Color خاموش شد"
            }
        }
        videoView = findViewById(R.id.videoView)
        val playerContainer = findViewById<FrameLayout>(R.id.playerContainer)
        // A real second-video preview sits above the source video and below the crop/placement handles.
        overlayVideoLayer = FrameLayout(this)
        overlayVideoLayer.visibility = View.GONE
        playerContainer.addView(overlayVideoLayer, FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT))
        overlayPreviewTexture = TextureView(this)
        overlayVideoLayer.addView(overlayPreviewTexture, FrameLayout.LayoutParams(1, 1))
        overlayPreviewTexture.surfaceTextureListener = object : TextureView.SurfaceTextureListener {
            override fun onSurfaceTextureAvailable(surfaceTexture: SurfaceTexture, width: Int, height: Int) {
                startOverlayPreviewOnSurface(surfaceTexture)
            }
            override fun onSurfaceTextureSizeChanged(surfaceTexture: SurfaceTexture, width: Int, height: Int) = updateOverlayPreviewLayout()
            override fun onSurfaceTextureDestroyed(surfaceTexture: SurfaceTexture): Boolean {
                releaseOverlayPreviewPlayer()
                return true
            }
            override fun onSurfaceTextureUpdated(surfaceTexture: SurfaceTexture) = Unit
        }
        cropOverlay = FreeCropOverlayView()
        playerContainer.addView(cropOverlay, FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT))
        placementOverlay = PlacementOverlayView(this, { xPct, yPct ->
            when (placementMode) {
                PlacementOverlayView.Mode.TEXT -> { textXPercent = xPct; textYPercent = yPct }
                PlacementOverlayView.Mode.VIDEO -> {
                    overlayVideoXPercent = xPct
                    overlayVideoYPercent = yPct
                    updateOverlayPreviewLayout()
                }
                else -> Unit
            }
        }, { newSize ->
            liveTextSize = newSize.coerceIn(8, 160)
            placementOverlay.setTextPreview(findViewById<EditText>(R.id.overlayTextInput).text.toString(), liveTextSize)
        }, { xPct, yPct, widthPct ->
            overlayVideoXPercent = xPct
            overlayVideoYPercent = yPct
            overlayVideoWidthPercent = widthPct.coerceIn(5, 90)
            updateOverlayPreviewLayout()
        })
        placementOverlay.visibility = View.GONE
        playerContainer.addView(placementOverlay, FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT))
        freeCropControls = findViewById(R.id.freeCropControls)
        findViewById<Button>(R.id.cropButton).setOnClickListener { toggleFreeCropMode() }
        findViewById<Button>(R.id.applyFreeCropButton).setOnClickListener {
            recordUndoState()
            readCropOverlay()
            if (!validCropMargins()) return@setOnClickListener
            cropSettingsSaved = true
            freeCropMode = false
            cropOverlay.visibility = View.GONE
            freeCropControls.visibility = View.GONE
            statusText.text = "محدودهٔ Free Crop ثبت شد: چپ $cropLeftPct٪، بالا $cropTopPct٪، راست $cropRightPct٪، پایین $cropBottomPct٪؛ برای ساخت فایل نهایی، دکمهٔ «خروجی تغییرات» را بزنید"
            Toast.makeText(this, "محدودهٔ برش آزاد ثبت شد", Toast.LENGTH_SHORT).show()
        }
        findViewById<Button>(R.id.outputFormatButton).setOnClickListener {
            outputContainerMatroska = !outputContainerMatroska
            findViewById<Button>(R.id.outputFormatButton).text = if (outputContainerMatroska) "فرمت: MKV" else "فرمت: MP4"
            statusText.text = if (outputContainerMatroska)
                "فرمت خروجی بدون رمزگذاری مجدد: MKV؛ ترک‌ها با FFmpeg کپی می‌شوند"
            else "فرمت خروجی بدون رمزگذاری مجدد: MP4"
        }

        val outputTargetSizeCheck = findViewById<CheckBox>(R.id.outputTargetSizeCheck)
        val targetSizeField = findViewById<EditText>(R.id.targetSizeMb)
        outputTargetSizeCheck.setOnCheckedChangeListener { _, checked ->
            targetSizeField.isEnabled = checked
            targetSizeField.alpha = if (checked) 1f else 0.45f
        }
        targetSizeField.isEnabled = outputTargetSizeCheck.isChecked

        val manualNameCheck = findViewById<CheckBox>(R.id.manualOutputNameCheck)
        val manualNameField = findViewById<EditText>(R.id.manualOutputName)
        manualNameField.visibility = View.GONE
        manualNameCheck.setOnCheckedChangeListener { _, checked ->
            manualOutputNameEnabled = checked
            manualNameField.visibility = if (checked) View.VISIBLE else View.GONE
            if (checked) manualNameField.requestFocus()
        }
        val tagCheck = findViewById<CheckBox>(R.id.tagMetadataCheck)
        val tagInput = findViewById<EditText>(R.id.tagMetadataInput)
        val tagPrefs = getSharedPreferences("veft_video_tags", MODE_PRIVATE)
        tagInput.setText(tagPrefs.getString("current_tag", ""))
        tagInput.visibility = View.GONE
        tagCheck.setOnCheckedChangeListener { _, checked ->
            tagInput.visibility = if (checked) View.VISIBLE else View.GONE
            if (checked) tagInput.requestFocus()
            tagPrefs.edit().putBoolean("tag_enabled", checked).apply()
        }
        tagInput.addTextChangedListener(object : android.text.TextWatcher {
            override fun beforeTextChanged(s: CharSequence?, start: Int, count: Int, after: Int) {}
            override fun onTextChanged(s: CharSequence?, start: Int, before: Int, count: Int) {
                tagPrefs.edit().putString("current_tag", s?.toString().orEmpty()).apply()
            }
            override fun afterTextChanged(s: android.text.Editable?) {}
        })
        tagCheck.isChecked = tagPrefs.getBoolean("tag_enabled", false)
        findViewById<Button>(R.id.videoInfoButton).setOnClickListener { showVideoInfoDialog() }
        installPlayerResizeHandle()

        playerColorPreview = findViewById(R.id.playerColorPreview)
        statusText = findViewById(R.id.statusText)
        emptyHint = findViewById(R.id.emptyHint)
        storyboardRows = findViewById(R.id.storyboardRows)
        fun storyboardScrollOffset(): Int {
            val scroll = findViewById<ScrollView>(R.id.mainScrollView)
            var node: View = storyboardRows
            var total = 0
            while (node.parent is View && node.parent !== scroll) {
                total += node.top
                node = node.parent as View
            }
            total += node.top
            return total
        }
        val storyboardTableScroll = findViewById<StoryboardDragScrollView>(R.id.storyboardTableScroll)
        val storyboardScrollbar = findViewById<StoryboardScrollbarView>(R.id.storyboardDragThumb)
        storyboardScrollbar.bind(storyboardTableScroll, storyboardRows)
        storyboardTableScroll.setOnScrollChangeListener { _, _, scrollY, _, _ ->
            val columns = storyboardColumns().coerceAtLeast(1)
            val firstRow = (0 until storyboardRows.childCount).firstOrNull { r -> storyboardRows.getChildAt(r).bottom > scrollY } ?: 0
            storyboardPriorityIndex = (firstRow * columns).coerceAtLeast(0)
            storyboardScrollbar.invalidate()
            this@MainActivity.updateToolbarRailHeight()
        }
        storyboardRows.addOnLayoutChangeListener { _, _, _, _, _, _, _, _, _ ->
            storyboardScrollbar.invalidate()
            this@MainActivity.updateToolbarRailHeight()
        }
        findViewById<View>(R.id.storyboardTableFrame).addOnLayoutChangeListener { _, _, _, _, _, _, _, _, _ ->
            storyboardScrollbar.invalidate()
            storyboardScrollbar.requestLayout()
        }
        storyboardTableScroll.setOnTouchListener { view, event ->
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN, MotionEvent.ACTION_MOVE -> view.parent?.requestDisallowInterceptTouchEvent(true)
                MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> view.parent?.requestDisallowInterceptTouchEvent(false)
            }
            false
        }
        findViewById<Button>(R.id.storyboardTopButton).text = "Between"
        findViewById<Button>(R.id.storyboardTopButton).setOnClickListener { button ->
            val navigationButton = button as Button
            when (storyboardNavigationMode) {
                0 -> storyboardTableScroll.smoothScrollTo(0, 0)
                1 -> storyboardTableScroll.post {
                    val maxScroll = (storyboardRows.height - storyboardTableScroll.height).coerceAtLeast(0)
                    storyboardTableScroll.smoothScrollTo(0, maxScroll / 2)
                }
                else -> storyboardTableScroll.post {
                    storyboardTableScroll.smoothScrollTo(0, (storyboardRows.height - storyboardTableScroll.height).coerceAtLeast(0))
                }
            }
            storyboardNavigationMode = (storyboardNavigationMode + 1) % 3
            navigationButton.text = when (storyboardNavigationMode) {
                0 -> "Up"
                1 -> "Between"
                else -> "Down"
            }
        }
        storyboardScaleDetector = android.view.ScaleGestureDetector(this, object : android.view.ScaleGestureDetector.SimpleOnScaleGestureListener() {
            override fun onScale(detector: android.view.ScaleGestureDetector): Boolean {
                val current = pendingStoryboardColumns ?: storyboardColumns()
                pendingStoryboardColumns = (current / detector.scaleFactor).toInt().coerceIn(1, 15)
                return true
            }
            override fun onScaleEnd(detector: android.view.ScaleGestureDetector) {
                pendingStoryboardColumns?.let { columns ->
                    userStoryboardColumns = columns
                    pendingStoryboardColumns = null
                    val uri = selectedUri
                    if (uri != null && videoDurationMs > 0L) reloadStoryboardForRange(uri) else buildEmptyStoryboard()
                    statusText.text = "بزرگ‌نمایی استوری‌بورد تنظیم شد؛ تعداد ستون‌ها: $columns"
                }
            }
        })
        val columnSpinner = findViewById<android.widget.Spinner>(R.id.storyboardColumnCountSpinner)
        val columnOptions = (2..15).map { it.toString() }
        columnSpinner.adapter = object : android.widget.ArrayAdapter<String>(this, android.R.layout.simple_spinner_item, columnOptions) {
            override fun getView(position: Int, convertView: View?, parent: ViewGroup): View {
                val label = (convertView as? TextView) ?: TextView(this@MainActivity)
                label.text = getItem(position)
                label.setTextSize(android.util.TypedValue.COMPLEX_UNIT_SP, 24f)
                label.setTypeface(null, Typeface.BOLD)
                label.gravity = Gravity.CENTER
                label.setTextColor(Color.WHITE)
                return label
            }
            override fun getDropDownView(position: Int, convertView: View?, parent: ViewGroup): View {
                val label = (convertView as? TextView) ?: TextView(this@MainActivity)
                label.text = "${getItem(position)} ستون"
                label.setTextSize(android.util.TypedValue.COMPLEX_UNIT_SP, 18f)
                label.setTypeface(null, Typeface.BOLD)
                label.gravity = Gravity.CENTER
                label.setTextColor(Color.WHITE)
                label.setPadding(dp(12), dp(10), dp(12), dp(10))
                label.setBackgroundColor(Color.rgb(16, 33, 62))
                return label
            }
        }.also { it.setDropDownViewResource(android.R.layout.simple_spinner_dropdown_item) }
        columnSpinner.scaleX = 1.15f
        columnSpinner.scaleY = 1.15f
        columnSpinner.setSelection(3) // default 5 columns
        columnSpinner.onItemSelectedListener = object : android.widget.AdapterView.OnItemSelectedListener {
            override fun onNothingSelected(parent: android.widget.AdapterView<*>?) = Unit
            override fun onItemSelected(parent: android.widget.AdapterView<*>?, view: View?, position: Int, id: Long) {
                val next = position + 2
                if (userStoryboardColumns == next) return
                userStoryboardColumns = next
                val scroll = findViewById<ScrollView>(R.id.mainScrollView)
                val oldY = scroll.scrollY
                val uri = selectedUri
                if (uri != null && videoDurationMs > 0L) reloadStoryboardForRange(uri) else buildEmptyStoryboard()
                // Rebuild changes the storyboard's measured height. Restore the previous
                // viewport after the new child tree has completed layout, not before it.
                scroll.viewTreeObserver.addOnPreDrawListener(object : android.view.ViewTreeObserver.OnPreDrawListener {
                    override fun onPreDraw(): Boolean {
                        if (scroll.viewTreeObserver.isAlive) scroll.viewTreeObserver.removeOnPreDrawListener(this)
                        scroll.post {
                            val maxY = ((scroll.getChildAt(0)?.height ?: 0) - scroll.height).coerceAtLeast(0)
                            scroll.scrollTo(0, oldY.coerceIn(0, maxY))
                        }
                        return true
                    }
                })
            }
        }
        findViewById<Button>(R.id.allViewButton).setOnClickListener { setAllViewMode(!allViewMode) }
        selectionText = findViewById(R.id.selectionText)
        findViewById<CheckBox>(R.id.storyboardCoverCheck).setOnCheckedChangeListener { _, checked ->
            storyboardCoverMode = checked
            if (!checked) selectedCoverFrameIndex = null
            statusText.text = if (checked) "حالت انتخاب کاور روشن است؛ اسلاید دلخواه را لمس کنید تا تصویر شاخص خروجی شود." else "حالت انتخاب کاور خاموش شد؛ کاور پیش‌فرض ویدیو استفاده می‌شود."
            updateSelectionText()
        }
        timeModeButton = findViewById(R.id.showTimelineButton)
        timelineView = findViewById(R.id.timelineView)
        trackTimelineView = findViewById(R.id.trackTimelineView)
        trackTimelineView.onClipSelected = { clip ->
            selectedTrackClipId = clip?.id
            statusText.text = clip?.let { "ترک انتخابی: ${it.name} • برای انتخاب چند ترک، هر ترک را نگه دارید؛ کشیدن وسط = جابه‌جایی، لبه‌ها = برش" }
                ?: "ترکی انتخاب نشده است"
        }
        trackTimelineView.onClipsChanged = { changed ->
            trackClips.clear(); trackClips.addAll(changed)
            selectedTrackClipId = trackTimelineView.selectedClipId
            syncLegacyTrackUris()
        }
        findViewById<Button>(R.id.splitTrackButton).setOnClickListener { splitSelectedTrackClip() }
        findViewById<Button>(R.id.deleteTrackButton).setOnClickListener { deleteSelectedTrackClip() }
        findViewById<Button>(R.id.resetTracksButton).setOnClickListener {
            recordUndoState()
            trackClips.clear(); selectedTrackClipId = null; externalAudioUri = null; externalSubtitleUri = null
            trackTimelineView.setClips(emptyList(), videoDurationMs)
            findViewById<Button>(R.id.addAudioButton).text = "افزودن صدا"
            findViewById<Button>(R.id.addSubtitleButton).text = "افزودن زیرنویس"
            statusText.text = "همهٔ ترک‌های افزوده‌شده پاک شدند"
        }
        timelineView.onSeek = { timeMs ->
            try { videoView.seekTo(timeMs.coerceIn(0L, videoDurationMs).toInt()) } catch (_: Exception) { }
            timelineView.setPlayhead(timeMs)
            updateStoryboardPlaybackHighlight(timeMs)
        }
        timelineView.onSelectRange = { range ->
            selectedTimelineRange = range
            statusText.text = "قطعهٔ انتخابی: ${formatTime(range.first)} تا ${formatTime(range.second)}"
        }
        findViewById<Button>(R.id.splitTimelineButton).setOnClickListener {
            if (videoDurationMs <= 0L) { Toast.makeText(this, "ابتدا ویدیو انتخاب کنید", Toast.LENGTH_SHORT).show(); return@setOnClickListener }
            if (videoDurationMs < 2L) { Toast.makeText(this, "مدت ویدیو برای برش کافی نیست", Toast.LENGTH_SHORT).show(); return@setOnClickListener }
            // Cut at the actual player position at the instant the button is tapped,
            // not the last position manually selected on the timeline.
            val currentPosition = try { videoView.currentPosition.toLong() } catch (_: Exception) { timelineView.playheadMs }
            if (currentPosition <= 0L || currentPosition >= videoDurationMs) {
                Toast.makeText(this, "ویدیو را به زمان موردنظر پخش یا جابه‌جا کنید و دوباره Cut بزنید", Toast.LENGTH_SHORT).show()
                return@setOnClickListener
            }
            val at = currentPosition.coerceIn(1L, videoDurationMs - 1L)
            if (!timelineSplitPoints.contains(at)) recordUndoState()
            if (timelineSplitPoints.add(at)) {
                timelineView.setPlayhead(at)
                timelineView.setTimeline(videoDurationMs, timelineSplitPoints.toList(), deletedTimelineRanges)
                trackTimelineView.setClips(trackClips.toList(), videoDurationMs)
                selectedTimelineRange = null
                statusText.text = "Cut ثبت شد: ${formatTime(at)}؛ با هر بار زدن، برش دیگری در زمان فعلی پخش ثبت می‌شود"
            } else Toast.makeText(this, "در این زمان برشی ثبت شده است", Toast.LENGTH_SHORT).show()
        }
        // secondCutButton and autoCropButton were removed from the visible layout;
        // do not bind listeners to views that no longer exist.
        findViewById<Button>(R.id.deleteTimelineSegmentButton).setOnClickListener {
            val range = selectedTimelineRange
            if (range == null) { Toast.makeText(this, "ابتدا یک قطعه از نوار زمان را انتخاب کنید", Toast.LENGTH_SHORT).show(); return@setOnClickListener }
            if (deletedTimelineRanges.none { it.first == range.first && it.second == range.second }) deletedTimelineRanges.add(range)
            selectedTimelineRange = null
            timelineView.setTimeline(videoDurationMs, timelineSplitPoints.toList(), deletedTimelineRanges)
                trackTimelineView.setClips(trackClips.toList(), videoDurationMs)
            statusText.text = "قطعهٔ ${formatTime(range.first)} تا ${formatTime(range.second)} برای حذف از خروجی علامت خورد"
        }
        findViewById<Button>(R.id.restoreTimelineButton).setOnClickListener {
            deletedTimelineRanges.clear(); timelineSplitPoints.clear(); selectedTimelineRange = null
            timelineView.setTimeline(videoDurationMs, emptyList(), emptyList())
            statusText.text = "برش‌ها و حذف‌های نوار زمان بازگردانی شدند"
        }

        findViewById<Button>(R.id.openButton).setOnClickListener { chooseVideo() }
        val trackPanel = findViewById<View>(R.id.trackPanel)
        trackPanel.visibility = View.GONE
        findViewById<Button>(R.id.trackPanelButton).setOnClickListener {
            if (trackPanel.visibility != View.VISIBLE) recordUndoState()
            trackPanel.visibility = if (trackPanel.visibility == View.VISIBLE) View.GONE else View.VISIBLE
            if (trackPanel.visibility == View.VISIBLE) statusText.text = "ترک صدا، زیرنویس یا چند ویدیوی مستقل اضافه کنید؛ ویدیوها در ردیف VIDEO روی تصویر اصلی ترکیب می‌شوند"
        }
        findViewById<Button>(R.id.finishTrackPanelButton).setOnClickListener {
            trackPanel.visibility = View.GONE
            statusText.text = "تنظیم ترک‌ها حفظ شد؛ برای ویرایش دوباره دکمهٔ «ترک‌ها» را بزنید"
        }
        findViewById<Button>(R.id.addAudioButton).setOnClickListener {
            statusText.text = "در حال باز کردن انتخاب‌گر فایل صوتی…"
            chooseExternalAudio()
        }
        findViewById<Button>(R.id.addSubtitleButton).setOnClickListener { chooseExternalSubtitle() }
        findViewById<Button>(R.id.addVideoTrackButton).setOnClickListener {
            statusText.text = "ویدیوی جدید به‌عنوان ترک مستقل زیر ویدیوی اصلی اضافه می‌شود…"
            chooseVideoForTrack()
        }
        val textOverlayPanel = findViewById<View>(R.id.textOverlayPanel)
        textOverlayPanel.visibility = View.GONE
        findViewById<Button>(R.id.textPlacementButton).setOnClickListener {
            if (textOverlayPanel.visibility != View.VISIBLE) recordUndoState()
            textOverlayPanel.visibility = if (textOverlayPanel.visibility == View.VISIBLE) View.GONE else View.VISIBLE
            if (textOverlayPanel.visibility == View.VISIBLE) {
                val textInput = findViewById<EditText>(R.id.overlayTextInput)
                textInput.requestFocus()
                if (textInput.text.isNotBlank() && selectedUri != null) activatePlacementMode(PlacementOverlayView.Mode.TEXT)
                statusText.text = "متن را وارد کنید؛ برای جابه‌جایی روی پلیر بکشید و در پایان «پایان متن‌گذاری» را بزنید"
            } else if (placementMode == PlacementOverlayView.Mode.TEXT) {
                placementMode = PlacementOverlayView.Mode.NONE
                placementOverlay.visibility = View.GONE
            }
        }
        findViewById<Button>(R.id.finishTextPlacementButton).setOnClickListener {
            textOverlayPanel.visibility = View.GONE
            if (placementMode == PlacementOverlayView.Mode.TEXT) {
                placementMode = PlacementOverlayView.Mode.NONE
                placementOverlay.visibility = View.GONE
            }
            statusText.text = "تنظیم متن ذخیره شد؛ برای ویرایش دوباره دکمهٔ «متن‌گذاری» را بزنید"
        }
        val overlayVideoPanel = findViewById<View>(R.id.overlayVideoPanel)
        overlayVideoPanel.visibility = View.GONE
        findViewById<Button>(R.id.overlayVideoPanelButton).setOnClickListener {
            if (overlayVideoPanel.visibility != View.VISIBLE) recordUndoState()
            overlayVideoPanel.visibility = if (overlayVideoPanel.visibility == View.VISIBLE) View.GONE else View.VISIBLE
            if (overlayVideoPanel.visibility == View.VISIBLE) {
                statusText.text = "ویدیوی رویی را انتخاب کنید؛ پس از تنظیم، «پایان تنظیم ویدیوی رویی» را بزنید"
            }
        }
        findViewById<Button>(R.id.finishOverlayVideoButton).setOnClickListener {
            overlayVideoPanel.visibility = View.GONE
            if (placementMode == PlacementOverlayView.Mode.VIDEO) {
                placementMode = PlacementOverlayView.Mode.NONE
                placementOverlay.visibility = View.GONE
            }
            statusText.text = "تنظیم ویدیوی رویی حفظ شد؛ برای تغییر دوباره دکمهٔ «ویدیوی رویی» را بزنید"
        }
        findViewById<EditText>(R.id.overlayTextInput).addTextChangedListener(object : TextWatcher {
            override fun beforeTextChanged(s: CharSequence?, start: Int, count: Int, after: Int) = Unit
            override fun onTextChanged(s: CharSequence?, start: Int, before: Int, count: Int) { updateLiveTextPreview() }
            override fun afterTextChanged(s: Editable?) = Unit
        })
        findViewById<Button>(R.id.pickOverlayVideoButton).setOnClickListener {
            statusText.text = "در حال باز کردن انتخاب‌گر ویدیوی رویی…"
            chooseOverlayVideo()
        }
        findViewById<Button>(R.id.joinAfterButton).setOnClickListener { chooseVideosToAppend() }
        findViewById<Button>(R.id.mergeButton).setOnClickListener { if (mergeUris.isEmpty()) chooseVideosForMerge() else mergeSelectedVideos() }
        findViewById<Button>(R.id.vectorButton).setOnClickListener { chooseVideosForVector() }
        findViewById<Button>(R.id.advancedEditButton).setOnClickListener { showAdvancedEditDialog() }
        findViewById<Button>(R.id.imageSceneSearchButton).setOnClickListener { chooseReferenceImage() }
        findViewById<Button>(R.id.selectAllButton).setOnClickListener {
            if (selectedUri == null || videoDurationMs <= 0L) {
                Toast.makeText(this, "ابتدا یک ویدیو انتخاب کنید", Toast.LENGTH_SHORT).show()
                return@setOnClickListener
            }
            selectedFrames.clear()
            selectedFrames.addAll((0 until activeStoryboardFrameCount).filter { it !in deletedStoryboardFrames })
            refreshSelectionStyles()
            updateSelectionText()
        }
        findViewById<Button>(R.id.clearSelectionButton).setOnClickListener {
            selectedFrames.clear()
            refreshSelectionStyles()
            updateSelectionText()
        }
        findViewById<Button>(R.id.applyColorToSelectedButton).setOnClickListener { applyColorToSelectedFrames() }
        setupManualColorControls()
        val timelinePanel = findViewById<View>(R.id.timelinePanel)
        val timelineActionButtons = findViewById<View>(R.id.timelineActionButtons)
        timeModeButton.setOnClickListener {
            val show = timelinePanel.visibility != View.VISIBLE
            if (show) recordUndoState()
            timelinePanel.visibility = if (show) View.VISIBLE else View.GONE
            timelineActionButtons.visibility = if (show) View.VISIBLE else View.GONE
            findViewById<View>(R.id.storyboardTimeRangeRow).visibility = if (show) View.VISIBLE else View.GONE
            timeModeButton.text = if (show) "بستن نوار زمان" else "نمایش نوار زمان"
            if (show) timelinePanel.post { timelinePanel.requestLayout() }
        }
        findViewById<Button>(R.id.pickStoryboardStartButton).setOnClickListener { setStoryboardTimeFromPlayback(true) }
        findViewById<Button>(R.id.pickStoryboardEndButton).setOnClickListener { setStoryboardTimeFromPlayback(false) }

        val controller = MediaController(this)
        controller.setAnchorView(videoView)
        // Keep native playback controls square and at full size. The previous 0.35 Y scale
        // compressed their height and made the controls look stretched.
        controller.scaleX = 1.0f
        controller.scaleY = 1.0f
        controller.pivotY = 0f
        videoView.setMediaController(controller)
        videoView.setOnPreparedListener { mediaPlayer ->
            emptyHint.visibility = View.GONE
            playerColorPreview.visibility = View.GONE
            // Match the visible preview area to the source video's aspect ratio and center it.
            // Placement and crop overlays use the exact same bounds, so preview percentages
            // correspond to the actual encoded frame instead of the surrounding black area.
            playerContainer.post {
                updatePlayerViewport(mediaPlayer.videoWidth, mediaPlayer.videoHeight)
            }
            statusText.text = "ویدیو آمادهٔ پخش است"
            mainHandler.removeCallbacks(playbackSyncRunnable)
            mainHandler.post(playbackSyncRunnable)
            mediaPlayer.setOnVideoSizeChangedListener { _, width, height ->
                controller.setAnchorView(videoView)
                playerContainer.post { updatePlayerViewport(width, height) }
            }
        }
        videoView.setOnCompletionListener {
            mainHandler.removeCallbacks(playbackSyncRunnable)
            timelineView.setPlayhead(videoDurationMs)
            updateStoryboardPlaybackHighlight(videoDurationMs)
            statusText.text = "پخش تمام شد"
        }
        videoView.setOnErrorListener { _, what, extra ->
            statusText.text = "پخش این فایل ممکن نیست (خطا $what/$extra)"
            emptyHint.visibility = View.VISIBLE
            true
        }
        buildEmptyStoryboard()
        updateModeButtons()
        handleIncomingVideoIntent(intent)
    }

    /** Accepts one shared video for editing or multiple shared videos for Merge. */
    override fun onNewIntent(intent: Intent?) {
        super.onNewIntent(intent)
        setIntent(intent)
        handleIncomingVideoIntent(intent)
    }

    private fun handleIncomingVideoIntent(incoming: Intent?) {
        if (incoming == null) return
        val action = incoming.action
        if (action != Intent.ACTION_SEND && action != Intent.ACTION_SEND_MULTIPLE) return
        val uris = mutableListOf<Uri>()
        if (action == Intent.ACTION_SEND_MULTIPLE) {
            @Suppress("DEPRECATION")
            val streams = incoming.getParcelableArrayListExtra<android.os.Parcelable>(Intent.EXTRA_STREAM)
            streams?.forEach { (it as? Uri)?.let(uris::add) }
        } else {
            val uri = if (android.os.Build.VERSION.SDK_INT >= 33) {
                incoming.getParcelableExtra(Intent.EXTRA_STREAM, Uri::class.java)
            } else {
                @Suppress("DEPRECATION")
                incoming.getParcelableExtra<android.os.Parcelable>(Intent.EXTRA_STREAM) as? Uri
            }
            uri?.let(uris::add)
        }
        incoming.clipData?.let { clip ->
            for (i in 0 until clip.itemCount) clip.getItemAt(i).uri?.let { if (it !in uris) uris.add(it) }
        }
        if (uris.isEmpty()) {
            Toast.makeText(this, "ویدیوی اشتراک‌گذاری‌شده قابل دریافت نیست", Toast.LENGTH_LONG).show()
            return
        }
        if (uris.size > 1) {
            mergeUris.clear(); mergeUris.addAll(uris.distinct())
            findViewById<Button>(R.id.mergeButton).text = "Merge (${mergeUris.size})"
            statusText.text = "${mergeUris.size} ویدیو دریافت شد؛ برای ادغام، دکمهٔ Merge را بزنید"
            Toast.makeText(this, "ویدیوها به بخش Merge منتقل شدند", Toast.LENGTH_SHORT).show()
        } else {
            mergeUris.clear()
            loadSelectedVideo(uris.first(), false)
        }
    }

    private fun chooseVideosForVector() {
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE); type = "video/*"
            putExtra(Intent.EXTRA_ALLOW_MULTIPLE, true)
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        }
        startActivityForResult(intent, PICK_VECTOR_VIDEOS)
    }

    private fun showVectorPreview() {
        val count = vectorUris.size
        val cols = when (count) { 1 -> 1; 2, 3, 4 -> 2; else -> 3 }
        val rows = (count + cols - 1) / cols
        val grid = android.widget.GridLayout(this).apply {
            columnCount = cols; rowCount = rows
            setBackgroundColor(Color.BLACK)
            useDefaultMargins = false
            alignmentMode = android.widget.GridLayout.ALIGN_BOUNDS
        }
        val players = mutableListOf<VideoView>()
        vectorUris.forEachIndexed { index, uri ->
            val player = VideoView(this)
            val lp = android.widget.GridLayout.LayoutParams().apply {
                width = 0; height = 0
                columnSpec = android.widget.GridLayout.spec(index % cols, 1, 1f)
                rowSpec = android.widget.GridLayout.spec(index / cols, 1, 1f)
                setMargins(0, 0, 0, 0)
            }
            player.layoutParams = lp
            player.setVideoURI(uri)
            player.setOnPreparedListener { mp -> mp.isLooping = true }
            grid.addView(player); players.add(player)
        }
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(0, 0, 0, 0)
            addView(grid, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f))
            addView(TextView(this@MainActivity).apply {
                text = "پیش‌نمایش چیدمان فشرده: $count ویدیو • فاصلهٔ قاب‌ها صفر"
                setTextColor(Color.WHITE); textSize = 12f; gravity = Gravity.CENTER
                setPadding(4, 6, 4, 6)
            })
        }
        val dialog = AlertDialog.Builder(this).setTitle("Vector • پیش‌نمایش چیدمان")
            .setView(container)
            .setPositiveButton("پخش هم‌زمان", null)
            .setNeutralButton("انتخاب دوباره", null)
            .setNegativeButton("بستن", null).create()
        dialog.setOnShowListener {
            standardizeDialogButtons(dialog)
            dialog.window?.setLayout(ViewGroup.LayoutParams.MATCH_PARENT, (resources.displayMetrics.heightPixels * 0.78f).toInt())
            dialog.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener {
                players.forEach { it.seekTo(0); it.start() }
                statusText.text = "Vector: پیش‌نمایش $count ویدیو؛ قاب‌ها بدون فاصله هستند. خروجی ترکیبی هنوز در این نسخه پیاده‌سازی نشده است."
                Toast.makeText(this, "پخش پیش‌نمایش آغاز شد؛ خروجی ترکیبی هنوز آماده نیست", Toast.LENGTH_LONG).show()
            }
            dialog.getButton(AlertDialog.BUTTON_NEUTRAL).setOnClickListener { dialog.dismiss(); chooseVideosForVector() }
        }
        dialog.show()
    }

    private fun showAdvancedEditDialog() {
        // A non-modal floating panel lets the user keep interacting with the storyboard/player.
        val density = resources.displayMetrics.density
        val panel = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding((12 * density).toInt(), (8 * density).toInt(), (12 * density).toInt(), (8 * density).toInt())
            setBackgroundColor(Color.rgb(11, 27, 56))
        }
        val heading = TextView(this).apply {
            text = "ویرایش پیشرفته"
            setTextColor(Color.rgb(255, 210, 31))
            textSize = 16f
            gravity = Gravity.CENTER
            setPadding(0, 0, 0, (6 * density).toInt())
        }
        panel.addView(heading)
        fun addControl(label: String, maxValue: Int, initial: Int, onValue: (Int) -> Unit) {
            val valueLabel = TextView(this).apply {
                text = "$label: ${initial}%"; setTextColor(Color.WHITE); textSize = 13f
            }
            panel.addView(valueLabel)
            val row = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL }
            val bar = SeekBar(this).apply {
                max = maxValue; progress = initial
                setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
                    override fun onProgressChanged(seekBar: SeekBar?, progress: Int, fromUser: Boolean) {
                        valueLabel.text = "$label: ${progress}%"
                        onValue(progress)
                    }
                    override fun onStartTrackingTouch(seekBar: SeekBar?) {}
                    override fun onStopTrackingTouch(seekBar: SeekBar?) {}
                })
            }
            row.addView(bar, LinearLayout.LayoutParams(0, dp(56), 1f))
            row.addView(Button(this).apply {
                text = "Rest"; textSize = 10f; isAllCaps = false
                setTextColor(Color.rgb(7, 20, 47)); setBackgroundTintList(android.content.res.ColorStateList.valueOf(Color.rgb(255, 210, 31)))
                minWidth = 0; minimumWidth = 0; minHeight = 0; minimumHeight = 0
                setPadding(6, 0, 6, 0)
                setOnClickListener { bar.progress = initial; valueLabel.text = "$label: ${initial}%"; onValue(initial) }
            }, LinearLayout.LayoutParams((96 * density).toInt(), (72 * density).toInt()))
            panel.addView(row)
        }
        var brightness = 100; var contrast = 100; var gamma = 100
        addControl("نور", 200, 100) { brightness = it }
        addControl("کنتراست", 200, 100) { contrast = it }
        addControl("گاما", 300, 100) { gamma = it }
        val actions = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER }
        val applyButton = Button(this).apply {
            text = "اعمال"; textSize = 11f; setTextColor(Color.rgb(7, 20, 47))
            setBackgroundTintList(android.content.res.ColorStateList.valueOf(Color.rgb(67, 217, 163)))
            setOnClickListener { Toast.makeText(this@MainActivity, "مقادیر نور $brightness٪، کنتراست $contrast٪ و گاما $gamma٪ انتخاب شدند؛ اتصال این تنظیمات به موتور خروجی در نسخهٔ بعدی لازم است.", Toast.LENGTH_LONG).show() }
        }
        val closeButton = Button(this).apply {
            text = "بستن"; textSize = 11f; setTextColor(Color.WHITE)
            setBackgroundTintList(android.content.res.ColorStateList.valueOf(Color.rgb(65, 91, 130)))
        }
        actions.addView(applyButton, LinearLayout.LayoutParams(0, (44 * density).toInt(), 1f).apply { marginEnd = (4 * density).toInt() })
        actions.addView(closeButton, LinearLayout.LayoutParams(0, (44 * density).toInt(), 1f))
        panel.addView(actions)
        val scroll = ScrollView(this).apply {
            isFillViewport = true
            addView(panel)
        }
        val popup = PopupWindow(scroll, (minOf(420, (resources.displayMetrics.widthPixels / density * 0.90f).toInt()) * density).toInt(), ViewGroup.LayoutParams.WRAP_CONTENT, false).apply {
            isTouchable = true
            isFocusable = false
            isOutsideTouchable = false
            setBackgroundDrawable(GradientDrawable().apply {
                setColor(Color.rgb(11, 27, 56))
                cornerRadius = 12 * density
                setStroke((1 * density).toInt(), Color.rgb(255, 210, 31))
            })
            elevation = 12 * density
        }
        closeButton.setOnClickListener { popup.dismiss() }
        val root = findViewById<View>(R.id.mainRootLayout)
        popup.showAtLocation(root, Gravity.TOP or Gravity.END, (8 * density).toInt(), (72 * density).toInt())
        scroll.viewTreeObserver.addOnGlobalLayoutListener {
            if (scroll.isAttachedToWindow) standardizeControlTree(scroll)
        }
        var dragX = 0f
        var dragY = 0f
        var startX = 0
        var startY = 0
        heading.setOnTouchListener { _, event ->
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    dragX = event.rawX; dragY = event.rawY
                    val loc = IntArray(2); scroll.getLocationOnScreen(loc)
                    startX = loc[0]; startY = loc[1]; true
                }
                MotionEvent.ACTION_MOVE -> {
                    val nx = (startX + event.rawX - dragX).toInt().coerceIn(0, (resources.displayMetrics.widthPixels - popup.width).coerceAtLeast(0))
                    val ny = (startY + event.rawY - dragY).toInt().coerceIn(0, (resources.displayMetrics.heightPixels - dp(120)).coerceAtLeast(0))
                    popup.update(nx, ny); true
                }
                else -> true
            }
        }
    }

    private fun chooseVideosToAppend() {
        if (selectedUri == null) {
            Toast.makeText(this, "ابتدا ویدیوی اصلی را باز کنید؛ سپس Join را بزنید", Toast.LENGTH_LONG).show()
            return
        }
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE)
            type = "video/*"
            putExtra(Intent.EXTRA_ALLOW_MULTIPLE, true)
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        }
        try { startActivityForResult(intent, PICK_APPEND_VIDEOS) }
        catch (_: Exception) { Toast.makeText(this, "انتخاب‌گر ویدیو در دسترس نیست", Toast.LENGTH_LONG).show() }
    }

    private fun chooseVideosForMerge() {
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE)
            type = "video/*"
            putExtra(Intent.EXTRA_ALLOW_MULTIPLE, true)
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
        }
        startActivityForResult(intent, PICK_MERGE_VIDEOS)
    }

    @Deprecated("Uses Activity result callback for compatibility")
    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (resultCode != RESULT_OK || data == null) return
        if (requestCode == PICK_APPEND_VIDEOS) {
            val base = selectedUri
            if (base == null) {
                Toast.makeText(this, "ابتدا ویدیوی اصلی را انتخاب کنید", Toast.LENGTH_LONG).show()
                return
            }
            val picked = mutableListOf<Uri>()
            data.clipData?.let { clip -> for (i in 0 until clip.itemCount) picked.add(clip.getItemAt(i).uri) }
            data.data?.let { if (it !in picked) picked.add(it) }
            val ordered = (listOf(base) + picked).distinct()
            if (ordered.size < 2) {
                Toast.makeText(this, "یک یا چند ویدیوی متفاوت برای اتصال به انتهای ویدیوی اصلی انتخاب کنید", Toast.LENGTH_LONG).show()
                return
            }
            mergeUris.clear(); mergeUris.addAll(ordered)
            findViewById<Button>(R.id.mergeButton).text = "Join (${mergeUris.size})"
            statusText.text = "${ordered.size} ویدیو برای Join آماده شد؛ ویدیوی اصلی اول است. برای شروع اتصال، دوباره دکمهٔ Join را بزنید."
        } else if (requestCode == PICK_MERGE_VIDEOS) {
            val picked = mutableListOf<Uri>()
            data.clipData?.let { clip -> for (i in 0 until clip.itemCount) picked.add(clip.getItemAt(i).uri) }
            data.data?.let { if (it !in picked) picked.add(it) }
            mergeUris.clear(); mergeUris.addAll(picked.distinct())
            if (mergeUris.size < 2) {
                mergeUris.clear()
                Toast.makeText(this, "برای Merge حداقل دو ویدیو انتخاب کنید", Toast.LENGTH_LONG).show()
                return
            }
            findViewById<Button>(R.id.mergeButton).text = "Merge (${mergeUris.size})"
            statusText.text = "${mergeUris.size} ویدیو برای ادغام آماده است؛ دکمهٔ Merge را دوباره بزنید"
        } else if (requestCode == PICK_VECTOR_VIDEOS) {
            val picked = mutableListOf<Uri>()
            data.clipData?.let { clip -> for (i in 0 until clip.itemCount) picked.add(clip.getItemAt(i).uri) }
            data.data?.let { if (it !in picked) picked.add(it) }
            vectorUris.clear(); vectorUris.addAll(picked.distinct().take(6))
            if (vectorUris.isEmpty()) return
            showVectorPreview()
        } else if (requestCode == REQUEST_VIDEO) {
            val picked = collectPickedUris(data).distinct()
            if (picked.isEmpty()) return
            picked.forEach { uri ->
                try { contentResolver.takePersistableUriPermission(uri, Intent.FLAG_GRANT_READ_URI_PERMISSION) } catch (_: Exception) { }
            }
            importedVideoUris.clear()
            importedVideoUris.addAll(picked)
            loadSelectedVideo(picked.first(), true)
            if (picked.size > 1) {
                mergeUris.clear()
                mergeUris.addAll(picked)
                findViewById<Button>(R.id.mergeButton).text = "Merge (${mergeUris.size})"
                statusText.text = "${picked.size} ویدیو وارد شد؛ ویدیوی اول برای تدوین باز است و همهٔ ویدیوها برای ادغام چندتایی آماده‌اند. برای ساخت فایل ترکیبی، Merge را بزنید."
            } else {
                mergeUris.clear()
                findViewById<Button>(R.id.mergeButton).text = "Merge • چند ویدیو"
            }
        } else if (requestCode == PICK_EXTERNAL_AUDIO) {
            val picked = collectPickedUris(data)
            if (picked.isEmpty()) return
            picked.forEach { uri -> addTrackClip(uri, TrackClipKind.AUDIO) }
            findViewById<Button>(R.id.addAudioButton).text = "صداها (${trackClips.count { it.kind == TrackClipKind.AUDIO }}) ✓"
            statusText.text = "${picked.size} فایل صوتی به نوار ترک اضافه شد؛ لبه‌های هر قطعه را برای برش و وسط آن را برای جابه‌جایی بکشید."
        } else if (requestCode == PICK_TRACK_VIDEO) {
            val picked = collectPickedUris(data)
            if (picked.isEmpty()) return
            picked.forEach { uri -> addTrackClip(uri, TrackClipKind.VIDEO) }
            findViewById<Button>(R.id.addVideoTrackButton).text = "ویدیوها (${trackClips.count { it.kind == TrackClipKind.VIDEO }}) ✓"
            statusText.text = "${picked.size} ویدیو به ترک مستقل زیر ویدیوی اصلی اضافه شد؛ قطعه‌ها را در ردیف VIDEO جابه‌جا یا کوتاه کنید."
        } else if (requestCode == PICK_EXTERNAL_SUBTITLE) {
            val picked = collectPickedUris(data)
            if (picked.isEmpty()) return
            picked.forEach { uri -> addTrackClip(uri, TrackClipKind.SUBTITLE) }
            findViewById<Button>(R.id.addSubtitleButton).text = "زیرنویس‌ها (${trackClips.count { it.kind == TrackClipKind.SUBTITLE }}) ✓"
            statusText.text = "${picked.size} فایل زیرنویس به نوار ترک اضافه شد؛ برای جابه‌جایی یا برش، قطعه را انتخاب و بکشید."
        } else if (requestCode == PICK_OVERLAY_VIDEO) {
            val uri = data.data ?: data.clipData?.takeIf { it.itemCount > 0 }?.getItemAt(0)?.uri ?: return
            try { contentResolver.takePersistableUriPermission(uri, Intent.FLAG_GRANT_READ_URI_PERMISSION) } catch (_: Exception) { }
            // Verify that the provider actually lets us read the selected video before accepting it.
            try {
                contentResolver.openAssetFileDescriptor(uri, "r")?.use { descriptor ->
                    if (descriptor.length == 0L) throw IllegalStateException("فایل ویدیوی انتخابی خالی است")
                } ?: throw IllegalStateException("فایل انتخاب‌شده قابل خواندن نیست")
            } catch (e: Exception) {
                overlayVideoUri = null
                Toast.makeText(this, "ویدیوی رویی باز نشد: ${e.message ?: "دسترسی به فایل ناموفق بود"}", Toast.LENGTH_LONG).show()
                statusText.text = "انتخاب ویدیوی رویی ناموفق بود؛ فایل دیگری انتخاب کنید"
                return
            }
            recordUndoState()
            overlayVideoUri = uri
            findViewById<Button>(R.id.pickOverlayVideoButton).text = "ویدیوی رویی ✓"
            showOverlayVideoPreview(uri)
            activatePlacementMode(PlacementOverlayView.Mode.VIDEO)
            statusText.text = "ویدیوی رویی انتخاب شد؛ کادر آن از همین لحظه روی پلیر قابل جابه‌جایی و تغییر اندازه است. برای تثبیت Save را بزنید"
        } else if (requestCode == PICK_REFERENCE_IMAGE) {
            referenceImageUri = data.data ?: return
            if (selectedUri == null || videoDurationMs <= 0L) {
                Toast.makeText(this, "حالا ویدیوی موردنظر را انتخاب کنید؛ سپس دوباره جست‌وجو با عکس را بزنید", Toast.LENGTH_LONG).show()
                return
            }
            searchVideoForImage(referenceImageUri!!, selectedUri!!)
        }
    }

    private fun chooseReferenceImage() {
        if (selectedUri == null || videoDurationMs <= 0L) {
            Toast.makeText(this, "ابتدا ویدیویی انتخاب کنید", Toast.LENGTH_LONG).show()
            return
        }
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE)
            type = "image/*"
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        }
        try { startActivityForResult(intent, PICK_REFERENCE_IMAGE) }
        catch (_: Exception) { Toast.makeText(this, "انتخاب‌گر عکس در دسترس نیست", Toast.LENGTH_LONG).show() }
    }

    private data class ImageMatch(val timeMs: Long, val score: Double, val bitmap: Bitmap)

    private fun searchVideoForImage(imageUri: Uri, videoUri: Uri) {
        statusText.text = "در حال جست‌وجوی صحنه‌های مشابه عکس…"
        findViewById<Button>(R.id.imageSceneSearchButton).isEnabled = false
        worker.execute {
            var retriever: MediaMetadataRetriever? = null
            try {
                val ref = contentResolver.openInputStream(imageUri)?.use { BitmapFactoryCompat.decode(it) }
                    ?: throw IllegalStateException("خواندن عکس ناموفق بود")
                val refSmall = Bitmap.createScaledBitmap(ref, 32, 32, true)
                ref.recycle()
                retriever = MediaMetadataRetriever().apply { setDataSource(this@MainActivity, videoUri) }
                val duration = retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_DURATION)?.toLongOrNull() ?: 0L
                if (duration <= 0L) throw IllegalStateException("مدت ویدیو خوانده نشد")
                val matches = mutableListOf<ImageMatch>()
                var t = 0L
                while (t < duration) {
                    val frame = retriever.getFrameAtTime(t * 1000L, MediaMetadataRetriever.OPTION_CLOSEST_SYNC)
                    if (frame != null) {
                        val small = Bitmap.createScaledBitmap(frame, 32, 32, true)
                        val score = imageSimilarity(refSmall, small)
                        if (score >= 0.72) matches.add(ImageMatch(t, score, Bitmap.createScaledBitmap(frame, 240, 135, true)))
                        small.recycle(); frame.recycle()
                    }
                    t += 1000L
                }
                refSmall.recycle()
                val filtered = matches.sortedByDescending { it.score }.fold(mutableListOf<ImageMatch>()) { acc, item ->
                    if (acc.none { kotlin.math.abs(it.timeMs - item.timeMs) < 2500L }) acc.add(item)
                    acc
                }.sortedBy { it.timeMs }.take(60)
                mainHandler.post {
                    findViewById<Button>(R.id.imageSceneSearchButton).isEnabled = true
                    if (filtered.isEmpty()) {
                        statusText.text = "صحنهٔ مشابه تازه‌ای پیدا نشد؛ اسلایدهای فعلی حفظ شدند. عکس واضح‌تر یا فریم نزدیک‌تری انتخاب کنید."
                        Toast.makeText(this, "نتیجه‌ای پیدا نشد", Toast.LENGTH_SHORT).show()
                    } else {
                        showImageMatches(filtered)
                        statusText.text = "${filtered.size} صحنهٔ مشابه در اسلایدهای استوری‌بورد نمایش داده شد؛ برای رفتن به هر صحنه همان اسلاید را لمس کنید."
                    }
                }
            } catch (e: Exception) {
                mainHandler.post {
                    findViewById<Button>(R.id.imageSceneSearchButton).isEnabled = true
                    statusText.text = "جست‌وجوی عکس ناموفق بود: ${e.message ?: "خطا"}"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                }
            } finally { try { retriever?.release() } catch (_: Exception) { } }
        }
    }

    private fun imageSimilarity(a: Bitmap, b: Bitmap): Double {
        val pa = IntArray(32 * 32); val pb = IntArray(32 * 32)
        a.getPixels(pa, 0, 32, 0, 0, 32, 32); b.getPixels(pb, 0, 32, 0, 0, 32, 32)
        var diff = 0.0
        for (i in pa.indices) {
            val ca = pa[i]; val cb = pb[i]
            diff += (kotlin.math.abs(Color.red(ca)-Color.red(cb)) + kotlin.math.abs(Color.green(ca)-Color.green(cb)) + kotlin.math.abs(Color.blue(ca)-Color.blue(cb))) / 765.0
        }
        return 1.0 - diff / pa.size
    }

    /** Replaces the ordinary storyboard grid with image-search matches; cells are laid out in explicit rows. */
    private fun showImageMatches(matches: List<ImageMatch>) {
        if (matches.isEmpty()) return

        frameBitmaps.values.forEach { if (!it.isRecycled) it.recycle() }
        frameBitmaps.clear()
        imageSearchFrameTimes.clear()
        selectedFrames.clear()
        storyboardRangeAnchorIndex = null
        storyboardRows.removeAllViews()
        frameViews.clear()
        activeStoryboardFrameCount = matches.size

        // Keep the same user-selected grid geometry for image-search storyboard cells.
        val columns = storyboardColumns().coerceAtLeast(1)
        val cellHeight = storyboardCellHeight()
        val availableWidth = (storyboardRows.width.takeIf { it > 0 }
            ?: (resources.displayMetrics.widthPixels - dp(95)).coerceAtLeast(dp(150)))
        val cellWidth = (availableWidth / columns).coerceAtLeast(dp(32))
        matches.forEachIndexed { index, match ->
            imageSearchFrameTimes[index] = match.timeMs
            frameBitmaps[index] = match.bitmap
        }
        matches.indices.toList().chunked(columns).forEach { rowIndices ->
            val row = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
            }
            rowIndices.forEach { index ->
                val match = matches[index]
                val cell = makeFrameCell(index, match.bitmap, formatTime(match.timeMs))
                val params = LinearLayout.LayoutParams(cellWidth, cellHeight).apply {
                    setMargins(0, 0, 0, 0)
                }
                row.addView(cell, params)
                frameViews[index] = cell
            }
            storyboardRows.addView(row)
        }
        refreshRailStoryboard()
        updateSelectionText()
    }

    private object BitmapFactoryCompat {
        fun decode(input: java.io.InputStream): Bitmap? = android.graphics.BitmapFactory.decodeStream(input)
    }

    private fun mergeSelectedVideos() {
        val sources = mergeUris.toList()
        if (sources.size < 2) { chooseVideosForMerge(); return }
        val button = findViewById<Button>(R.id.mergeButton)
        button.isEnabled = false
        statusText.text = "در حال ادغام ${sources.size} ویدیو…"
        val output = File(cacheDir, "evc_merge_${System.currentTimeMillis()}.mp4")
        try {
            val items = sources.map { uri -> EditedMediaItem.Builder(MediaItem.fromUri(uri)).build() }
            val sequence = EditedMediaItemSequence.Builder(items).build()
            val composition = Composition.Builder(sequence).build()
            val transformer = Transformer.Builder(this).addListener(object : Transformer.Listener {
                override fun onCompleted(composition: Composition, exportResult: ExportResult) {
                    activeTransformer = null
                    try {
                        val values = ContentValues().apply {
                            put(MediaStore.Video.Media.DISPLAY_NAME, requestedOutputDisplayName("EVC_Merged_${System.currentTimeMillis()}", "mp4"))
                            put(MediaStore.Video.Media.MIME_TYPE, "video/mp4")
                            if (android.os.Build.VERSION.SDK_INT >= 29) {
                                put(MediaStore.Video.Media.RELATIVE_PATH, Environment.DIRECTORY_MOVIES + "/EVC")
                                put(MediaStore.Video.Media.IS_PENDING, 1)
                            }
                        }
                        val outUri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
                            ?: throw IllegalStateException("ساخت فایل در Movies/EVC ممکن نشد")
                        contentResolver.openOutputStream(outUri)?.use { out -> FileInputStream(output).use { it.copyTo(out) } }
                            ?: throw IllegalStateException("نوشتن فایل ادغام‌شده ناموفق بود")
                        if (android.os.Build.VERSION.SDK_INT >= 29) contentResolver.update(outUri, ContentValues().apply { put(MediaStore.Video.Media.IS_PENDING, 0) }, null, null)
                        writeOutputInfoReport(outUri)
                        output.delete(); mergeUris.clear(); button.text = "Merge"; button.isEnabled = true
                        statusText.text = "ویدیوها در Movies/EVC ادغام شدند"
                        Toast.makeText(this@MainActivity, "فایل ادغام‌شده ذخیره شد", Toast.LENGTH_LONG).show()
                    } catch (e: Exception) { output.delete(); button.isEnabled = true; statusText.text = "ذخیرهٔ Merge ناموفق بود: ${e.message}" }
                }
                override fun onError(composition: Composition, exportResult: ExportResult, exportException: ExportException) {
                    activeTransformer = null; output.delete(); button.isEnabled = true
                    statusText.text = "ادغام ناموفق بود: ${exportException.message ?: "خطای پردازش ویدیو"}"
                    Toast.makeText(this@MainActivity, statusText.text, Toast.LENGTH_LONG).show()
                }
            }).build()
            activeTransformer = transformer
            transformer.start(composition, output.absolutePath)
        } catch (e: Exception) {
            activeTransformer = null; output.delete(); button.isEnabled = true
            statusText.text = "شروع Merge ناموفق بود: ${e.message ?: "خطا"}"
        }
    }

    private fun loadSelectedVideo(uri: Uri, persistPermission: Boolean) {
        if (persistPermission) {
            try { contentResolver.takePersistableUriPermission(uri, Intent.FLAG_GRANT_READ_URI_PERMISSION) } catch (_: Exception) { }
        }
        selectedUri = uri
        mainHandler.removeCallbacks(storyboardAutoApplyRunnable)
        storyboardStartMs = 0L
        storyboardEndMs = 0L
        storyboardIntervalMs = null
        activeStoryboardFrameCount = DEFAULT_STORYBOARD_FRAME_COUNT
        suppressStoryboardAutoApply = true
        try { findViewById<EditText>(R.id.storyboardIntervalTime).setText("") }
        finally { suppressStoryboardAutoApply = false }
        findViewById<EditText>(R.id.overlayVideoStartTime).setText("00:00")
        findViewById<EditText>(R.id.overlayVideoEndTime).setText("99:59")
        timelineSplitPoints.clear()
        deletedTimelineRanges.clear()
        selectedTimelineRange = null
        timelineView.setTimeline(0L, emptyList(), emptyList())
        trackClips.clear(); selectedTrackClipId = null
        if (::trackTimelineView.isInitialized) trackTimelineView.setClips(emptyList(), 0L)
        externalAudioUri = null; externalSubtitleUri = null
        findViewById<Button>(R.id.addAudioButton).text = "افزودن صدا"
        findViewById<Button>(R.id.addSubtitleButton).text = "افزودن زیرنویس"
        timelineView.setThumbnails(emptyList())
        selectedFrames.clear()
        selectedCoverFrameIndex = null
        storyboardCoverMode = false
        findViewById<CheckBox>(R.id.storyboardCoverCheck).isChecked = false
        playbackFrameIndex = -1
        frameBitmaps.values.forEach { if (!it.isRecycled) it.recycle() }
        frameBitmaps.clear()
        previewBitmaps.values.forEach { if (!it.isRecycled) it.recycle() }
        previewBitmaps.clear()
        playerColorPreview.setImageDrawable(null)
        playerColorPreview.visibility = View.GONE
        deletedStoryboardFrames.clear()
        frameColorProfiles.clear()
        buildEmptyStoryboard()
        emptyHint.visibility = View.VISIBLE
        statusText.text = "در حال آماده‌سازی ویدیو و استخراج فریم‌ها…"
        videoView.setVideoURI(uri)
        videoView.requestFocus()
        loadStoryboard(uri)
    }

    /** Sets up manual RGB channel controls for the real video export. */
    private fun setupManualColorControls() {
        val red = findViewById<SeekBar>(R.id.redColorSeek)
        val green = findViewById<SeekBar>(R.id.greenColorSeek)
        val blue = findViewById<SeekBar>(R.id.blueColorSeek)
        val saturation = findViewById<SeekBar>(R.id.saturationSeek)
        val saturationValue = findViewById<TextView>(R.id.saturationValue)
        val redValue = findViewById<TextView>(R.id.redColorValue)
        val greenValue = findViewById<TextView>(R.id.greenColorValue)
        val blueValue = findViewById<TextView>(R.id.blueColorValue)
        fun updateLabels() {
            redValue.text = "قرمز ${"%.2f".format(java.util.Locale.US, red.progress / 100f)}"
            greenValue.text = "سبز ${"%.2f".format(java.util.Locale.US, green.progress / 100f)}"
            blueValue.text = "آبی ${"%.2f".format(java.util.Locale.US, blue.progress / 100f)}"
            saturationValue.text = "اشباع رنگ ${"%.2f".format(java.util.Locale.US, saturation.progress / 100f)}"
        }
        val listener = object : SeekBar.OnSeekBarChangeListener {
            override fun onProgressChanged(seekBar: SeekBar?, progress: Int, fromUser: Boolean) {
                updateLabels()
                if (fromUser) refreshLiveColorPreview()
            }
            override fun onStartTrackingTouch(seekBar: SeekBar?) {}
            override fun onStopTrackingTouch(seekBar: SeekBar?) {}
        }
        red.setOnSeekBarChangeListener(listener)
        green.setOnSeekBarChangeListener(listener)
        blue.setOnSeekBarChangeListener(listener)
        saturation.setOnSeekBarChangeListener(listener)

        // Each Reset button restores only its own control to neutral (1.00).
        fun bindReset(buttonId: Int, seekBar: SeekBar) {
            findViewById<Button>(buttonId).setOnClickListener {
                seekBar.progress = 100
                updateLabels()
                refreshLiveColorPreview()
            }
        }
        bindReset(R.id.resetRedColorButton, red)
        bindReset(R.id.resetGreenColorButton, green)
        bindReset(R.id.resetBlueColorButton, blue)
        bindReset(R.id.resetSaturationButton, saturation)
        updateLabels()
    }

    /** Save the current RGB combination for every selected storyboard interval. */
    private fun applyColorToSelectedFrames() {
        recordUndoState()
        if (selectedUri == null || videoDurationMs <= 0L) {
            Toast.makeText(this, "ابتدا ویدیو را انتخاب کنید", Toast.LENGTH_SHORT).show(); return
        }
        if (selectedFrames.isEmpty()) {
            Toast.makeText(this, "ابتدا یک یا چند اسلاید را انتخاب کنید", Toast.LENGTH_LONG).show(); return
        }
        val profile = currentRgbProfile()
        selectedFrames.forEach { frameColorProfiles[it] = profile }
        refreshLiveColorPreview()
        statusText.text = "ترکیب رنگ فعلی برای ${selectedFrames.size} اسلاید ذخیره شد؛ برای هر اسلاید می‌توان ترکیب دیگری ثبت کرد"
        Toast.makeText(this, "تنظیم رنگ برای ${selectedFrames.size} اسلاید ذخیره شد", Toast.LENGTH_SHORT).show()
    }

    /** Updates storyboard thumbnails immediately and shows a tinted still-frame overlay in the player. */
    private fun refreshLiveColorPreview() {
        val current = currentRgbProfile()
        for ((index, original) in frameBitmaps) {
            if (original.isRecycled) continue
            val profile = if (selectedFrames.isEmpty() || index in selectedFrames) current else frameColorProfiles[index] ?: RgbProfile(1f, 1f, 1f, 1f)
            val tinted = tintBitmap(original, profile)
            previewBitmaps.put(index, tinted)?.let { old -> if (!old.isRecycled) old.recycle() }
            val cell = frameViews[index]
            val image = cell?.let { container ->
                (0 until container.childCount).mapNotNull { container.getChildAt(it) as? ImageView }.firstOrNull()
            }
            image?.setImageBitmap(tinted)
        }
        val source = selectedUri ?: run { playerColorPreview.visibility = View.GONE; return }
        val request = ++playerPreviewRequest
        val position = try { videoView.currentPosition.toLong().coerceAtLeast(0L) } catch (_: Exception) { 0L }
        playerColorPreview.visibility = View.VISIBLE
        statusText.text = "پیش‌نمایش زندهٔ رنگ در حال به‌روزرسانی است…"
        worker.execute {
            var retriever: MediaMetadataRetriever? = null
            try {
                retriever = MediaMetadataRetriever()
                retriever.setDataSource(this, source)
                val frame = retriever.getFrameAtTime(position * 1000L, MediaMetadataRetriever.OPTION_CLOSEST_SYNC)
                if (frame != null) {
                    val tinted = tintBitmap(frame, current)
                    if (!frame.isRecycled) frame.recycle()
                    mainHandler.post {
                        if (request == playerPreviewRequest && !isFinishing) {
                            playerColorPreview.setImageBitmap(tinted)
                            playerColorPreview.visibility = View.VISIBLE
                            statusText.text = "پیش‌نمایش رنگ روی اسلایدها و فریم فعلی پلیر به‌روز شد"
                        } else if (!tinted.isRecycled) tinted.recycle()
                    }
                }
            } catch (_: Exception) {
                mainHandler.post {
                    if (request == playerPreviewRequest) {
                        playerColorPreview.visibility = View.GONE
                        statusText.text = "پیش‌نمایش اسلایدها به‌روز شد؛ گرفتن فریم پلیر ممکن نشد"
                    }
                }
            } finally { try { retriever?.release() } catch (_: Exception) {} }
        }
    }

    private fun tintBitmap(source: Bitmap, profile: RgbProfile): Bitmap {
        val w = source.width
        val h = source.height
        val pixels = IntArray(w * h)
        source.getPixels(pixels, 0, w, 0, 0, w, h)
        for (i in pixels.indices) {
            val c = pixels[i]
            val r = (Color.red(c) * profile.red).coerceIn(0f, 255f)
            val g = (Color.green(c) * profile.green).coerceIn(0f, 255f)
            val b = (Color.blue(c) * profile.blue).coerceIn(0f, 255f)
            val gray = 0.213f * r + 0.715f * g + 0.072f * b
            val sat = profile.saturation
            pixels[i] = Color.argb(Color.alpha(c),
                (gray + (r - gray) * sat).toInt().coerceIn(0, 255),
                (gray + (g - gray) * sat).toInt().coerceIn(0, 255),
                (gray + (b - gray) * sat).toInt().coerceIn(0, 255))
        }
        return Bitmap.createBitmap(w, h, Bitmap.Config.ARGB_8888).also { it.setPixels(pixels, 0, w, 0, 0, w, h) }
    }

    private fun currentRgbProfile() = RgbProfile(
        findViewById<SeekBar>(R.id.redColorSeek).progress / 100f,
        findViewById<SeekBar>(R.id.greenColorSeek).progress / 100f,
        findViewById<SeekBar>(R.id.blueColorSeek).progress / 100f,
        findViewById<SeekBar>(R.id.saturationSeek).progress / 100f
    )

    /** Exports the full video with an independently saved RGB effect for each storyboard interval. */
    private fun exportColorizedVideo() {
        val source = selectedUri
        if (source == null || videoDurationMs <= 0L) {
            Toast.makeText(this, "ابتدا یک ویدیوی معتبر انتخاب کنید", Toast.LENGTH_LONG).show(); return
        }
        val sizeField = findViewById<android.widget.EditText>(R.id.targetSizeMb)
        val targetMb = sizeField.text.toString().trim().replace(',', '.').toFloatOrNull()
        if (targetMb == null || targetMb < 1f || targetMb > 4096f) {
            sizeField.error = "حجم هدف را بین 1 تا 4096 مگابایت وارد کنید"; return
        }
        val button = findViewById<Button>(R.id.outputChangesButton)
        button.isEnabled = false
        statusText.text = "در حال ساخت خروجی با اعمال تغییرات رنگ و حجم هدف؛ رمزگذاری مجدد انجام می‌شود…"
        val output = File(cacheDir, "evc_colorized_${System.currentTimeMillis()}.mp4")
        try {
            val total = activeStoryboardFrameCount
            val rangeStart = storyboardStartMs.coerceIn(0L, videoDurationMs)
            val rangeEnd = (if (storyboardEndMs > rangeStart) storyboardEndMs else videoDurationMs)
                .coerceIn(rangeStart, videoDurationMs)
            if (rangeEnd <= rangeStart) throw IllegalStateException("بازهٔ زمانی استوری‌بورد معتبر نیست")

            // Export only intervals for which the user explicitly saved a color profile.
            // Do not add neutral/unselected storyboard intervals to this output.
            val coloredIndices = frameColorProfiles.keys
                .filter { it in 0 until total && it !in deletedStoryboardFrames }
                .sorted()
            val intervals = coloredIndices.mapNotNull { index ->
                val startMs = storyboardTimestampForIndex(index, total, rangeStart, rangeEnd)
                val endMs = if (storyboardIntervalMs != null && storyboardIntervalMs!! > 0L) {
                    minOf(rangeEnd, startMs + storyboardIntervalMs!!)
                } else if (index + 1 < total) {
                    minOf(rangeEnd, storyboardTimestampForIndex(index + 1, total, rangeStart, rangeEnd))
                } else rangeEnd
                if (startMs >= rangeEnd || endMs <= startMs) null else Triple(index, startMs, endMs)
            }
            val items = intervals.map { (index, startMs, endMs) ->
                val profile = frameColorProfiles[index] ?: throw IllegalStateException("تنظیم رنگ اسلاید پیدا نشد")
                val effect = RgbAdjustment.Builder()
                    .setRedScale(profile.red).setGreenScale(profile.green).setBlueScale(profile.blue).build()
                val saturationEffect = HslAdjustment.Builder().adjustSaturation(((profile.saturation - 1f) * 100f).coerceIn(-100f, 100f)).build()
                val clippedMedia = MediaItem.Builder().setUri(source)
                    .setClippingConfiguration(MediaItem.ClippingConfiguration.Builder()
                        .setStartPositionMs(startMs).setEndPositionMs(endMs).build()).build()
                EditedMediaItem.Builder(clippedMedia).setEffects(Effects(emptyList(), listOf(effect, saturationEffect))).build()
            }
            if (items.isEmpty()) throw IllegalStateException("ابتدا برای اسلایدهای موردنظر تنظیم رنگ ذخیره کنید؛ هیچ بازهٔ رنگی برای خروجی وجود ندارد")
            val selectedDurationMs = intervals.sumOf { it.third - it.second }.coerceAtLeast(1L)
            // Estimate bitrate from the total duration of colored intervals, not the full source video.
            val totalBitsPerSecond = (targetMb.toDouble() * 1024.0 * 1024.0 * 8.0 / (selectedDurationMs / 1000.0)).toInt()
            val videoBitrate = (totalBitsPerSecond - 128_000).coerceIn(200_000, 20_000_000)
            val encoderFactory = DefaultEncoderFactory.Builder(this)
                .setRequestedVideoEncoderSettings(VideoEncoderSettings.Builder().setBitrate(videoBitrate).build())
                .build()
            val composition = Composition.Builder(EditedMediaItemSequence.Builder(items).build()).build()
            val transformer = Transformer.Builder(this)
                .setEncoderFactory(encoderFactory)
                .addListener(object : Transformer.Listener {
                    override fun onCompleted(composition: Composition, exportResult: ExportResult) {
                        activeTransformer = null
                        button.isEnabled = true
                        try {
                            val values = ContentValues().apply {
                                put(MediaStore.Video.Media.DISPLAY_NAME, requestedOutputDisplayName("EVC_colored_intervals_${System.currentTimeMillis()}", "mp4"))
                                put(MediaStore.Video.Media.MIME_TYPE, "video/mp4")
                                if (android.os.Build.VERSION.SDK_INT >= 29) {
                                    put(MediaStore.Video.Media.RELATIVE_PATH, Environment.DIRECTORY_MOVIES + "/EVC")
                                    put(MediaStore.Video.Media.IS_PENDING, 1)
                                }
                            }
                            val outUri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
                                ?: throw IllegalStateException("ساخت فایل در Movies/EVC ممکن نشد")
                            contentResolver.openOutputStream(outUri)?.use { out -> FileInputStream(output).use { it.copyTo(out) } }
                                ?: throw IllegalStateException("نوشتن فایل خروجی ناموفق بود")
                            if (android.os.Build.VERSION.SDK_INT >= 29) contentResolver.update(outUri, ContentValues().apply {
                                put(MediaStore.Video.Media.IS_PENDING, 0)
                            }, null, null)
                            writeOutputInfoReport(outUri)
                            output.delete()
                    restoreNormalStoryboardAfterExport()
                            statusText.text = "فقط ${intervals.size} بازهٔ دارای تنظیم رنگ در Movies/EVC ذخیره شد؛ حجم هدف حدود ${targetMb} MB بود و رمزگذاری مجدد انجام شد."
                            Toast.makeText(this@MainActivity, "فقط بازه‌های رنگ‌گذاری‌شده ذخیره شدند؛ حجم نهایی ممکن است با هدف تفاوت داشته باشد", Toast.LENGTH_LONG).show()
                        } catch (e: Exception) {
                            output.delete(); statusText.text = "ذخیرهٔ خروجی ناموفق بود: ${e.message ?: "خطا"}"
                            Toast.makeText(this@MainActivity, statusText.text, Toast.LENGTH_LONG).show()
                        }
                    }
                    override fun onError(composition: Composition, exportResult: ExportResult, exportException: ExportException) {
                        activeTransformer = null; output.delete(); button.isEnabled = true
                        statusText.text = "خروجی رنگی ناموفق بود: ${exportException.message ?: "خطای رمزگذاری"}"
                        Toast.makeText(this@MainActivity, statusText.text, Toast.LENGTH_LONG).show()
                    }
                }).build()
            activeTransformer = transformer
            transformer.start(composition, output.absolutePath)
        } catch (e: Exception) {
            activeTransformer = null; output.delete(); button.isEnabled = true
            statusText.text = "شروع خروجی رنگی ناموفق بود: ${e.message ?: "خطا"}"
            Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
        }
    }

    // Experimental thumbnail-only colorization preview. It does not alter the source video
    // or the exported video; this first prototype uses luminance heuristics, not AI segmentation.
    private fun colorizeStoryboardPreview() {
        if (frameBitmaps.isEmpty()) {
            Toast.makeText(this, "ابتدا ویدیو را انتخاب کنید و منتظر استخراج اسلایدها بمانید", Toast.LENGTH_LONG).show()
            return
        }
        var processed = 0
        for ((index, original) in frameBitmaps) {
            if (original.isRecycled) continue
            val w = original.width
            val h = original.height
            val pixels = IntArray(w * h)
            original.getPixels(pixels, 0, w, 0, 0, w, h)
            for (i in pixels.indices) {
                val c = pixels[i]
                val r = Color.red(c)
                val g = Color.green(c)
                val b = Color.blue(c)
                val y = (0.299 * r + 0.587 * g + 0.114 * b).toInt()
                val chroma = maxOf(r, g, b) - minOf(r, g, b)
                if (chroma < 28 && y in 35..220) {
                    // Heuristic only: mid/darker tones receive a restrained green tint;
                    // brighter midtones receive a restrained warm tint.
                    pixels[i] = if (y < 118) {
                        Color.rgb((y * 0.72).toInt().coerceIn(0,255),
                                  (y * 1.08 + 8).toInt().coerceIn(0,255),
                                  (y * 0.70).toInt().coerceIn(0,255))
                    } else {
                        Color.rgb((y * 1.10 + 12).toInt().coerceIn(0,255),
                                  (y * 0.88 + 5).toInt().coerceIn(0,255),
                                  (y * 0.72).toInt().coerceIn(0,255))
                    }
                }
            }
            val preview = Bitmap.createBitmap(w, h, Bitmap.Config.ARGB_8888)
            preview.setPixels(pixels, 0, w, 0, 0, w, h)
            val cell = frameViews[index]
            val image = cell?.let { container ->
                (0 until container.childCount).mapNotNull { container.getChildAt(it) as? ImageView }.firstOrNull()
            }
            image?.setImageBitmap(preview)
            processed++
        }
        statusText.text = "پیش‌نمایش رنگی‌سازی آزمایشی روی $processed اسلاید اعمال شد؛ ویدیوی اصلی و خروجی تغییر نکرده‌اند"
        Toast.makeText(this, "این نسخه فقط پیش‌نمایش اسلایدها را رنگی می‌کند؛ خروجی ویدیویی رنگی هنوز فعال نیست", Toast.LENGTH_LONG).show()
    }

    private fun collectPickedUris(data: Intent): List<Uri> {
        val picked = mutableListOf<Uri>()
        data.clipData?.let { clip -> for (i in 0 until clip.itemCount) picked.add(clip.getItemAt(i).uri) }
        data.data?.let { if (it !in picked) picked.add(it) }
        picked.distinct().forEach { uri ->
            try { contentResolver.takePersistableUriPermission(uri, Intent.FLAG_GRANT_READ_URI_PERMISSION) } catch (_: Exception) { }
        }
        return picked
    }

    private fun addTrackClip(uri: Uri, kind: TrackClipKind) {
        val name = displayNameForUri(uri)
        val sourceDuration = if (kind == TrackClipKind.AUDIO || kind == TrackClipKind.VIDEO) {
            try {
                val retriever = MediaMetadataRetriever()
                retriever.setDataSource(this, uri)
                val duration = retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_DURATION)?.toLongOrNull() ?: videoDurationMs
                retriever.release()
                duration.coerceAtLeast(1000L)
            } catch (_: Exception) { videoDurationMs.coerceAtLeast(1000L) }
        } else videoDurationMs.coerceAtLeast(1000L)
        val playhead = try { videoView.currentPosition.toLong() } catch (_: Exception) { timelineView.playheadMs }
        val clip = TrackClip(nextTrackClipId++, uri, kind, name, playhead.coerceAtLeast(0L), 0L,
            minOf(sourceDuration, (videoDurationMs - playhead).coerceAtLeast(1000L)).coerceAtLeast(1000L), sourceDuration)
        trackClips.add(clip)
        selectedTrackClipId = clip.id
        trackTimelineView.setClips(trackClips.toList(), videoDurationMs)
        trackTimelineView.selectClip(clip.id)
        syncLegacyTrackUris()
    }

    private fun syncLegacyTrackUris() {
        externalAudioUri = trackClips.firstOrNull { it.kind == TrackClipKind.AUDIO }?.uri
        externalSubtitleUri = trackClips.firstOrNull { it.kind == TrackClipKind.SUBTITLE }?.uri
    }

    private fun formatTrackTime(ms: Long): String {
        val seconds = (ms.coerceAtLeast(0L) / 1000L)
        return String.format(java.util.Locale.US, "%02d:%02d", seconds / 60, seconds % 60)
    }

    private fun captureEditorHistoryState() = EditorHistoryState(timelineSplitPoints.toList(), deletedTimelineRanges.toList(), trackClips.toList(), frameColorProfiles.toMap(), listOf(cropLeftPct, cropTopPct, cropRightPct, cropBottomPct), cropSettingsSaved, autoColorEnabled, overlayVideoUri, findViewById<EditText>(R.id.overlayTextInput).text.toString(), textXPercent, textYPercent, liveTextSize, overlayVideoXPercent, overlayVideoYPercent, overlayVideoWidthPercent, mergeUris.toList(), vectorUris.toList(), referenceImageUri)

    /** Keep one visible Undo and one visible Redo action, even if a layout revision accidentally duplicates them. */
    /**
     * Move only the storyboard table inside its own movement area. The storyboard action
     * rows stay in their original fixed position above the table.
     */
    /** Keep the draggable tool rail full-height so the storyboard thumbnail strip can use its lower area. */
    /** Keeps the storyboard viewport flush with the bottom of the available editor area. */
    private fun updateToolbarRailHeight() {
        val scroll = findViewById<ScrollView>(R.id.mainScrollView) ?: return
        val section = findViewById<View>(R.id.storyboardSection) ?: return
        val moveArea = findViewById<View>(R.id.storyboardTableMoveArea) ?: return
        if (scroll.height <= 0) return
        scroll.post {
            section.post sectionPost@{
                if (scroll.height <= 0 || moveArea.parent == null) return@sectionPost
                val sectionTopInScroll = section.top - scroll.scrollY
                val remaining = (scroll.height - sectionTopInScroll - moveArea.top - dp(2))
                    .coerceAtLeast(dp(180))
                val current = moveArea.layoutParams
                if (current.height != remaining) {
                    current.height = remaining
                    moveArea.layoutParams = current
                    moveArea.requestLayout()
                }
            }
        }
    }

    private fun setupDraggableToolbarRail() {
        val root = findViewById<LinearLayout>(R.id.mainRootLayout)
        val rail = findViewById<LinearLayout>(R.id.standaloneActionsRail)
        val handle = findViewById<TextView>(R.id.toolbarDragHandle)
        val editor = findViewById<LinearLayout>(R.id.editorContentColumn)
        val horizontalScroll = findViewById<android.widget.HorizontalScrollView>(R.id.toolbarHorizontalScroll)
        val verticalScroll = findViewById<ScrollView>(R.id.toolbarVerticalScroll)
        val actionContainer = findViewById<LinearLayout>(R.id.standaloneActionsContainer)
        val verticalContainer = findViewById<LinearLayout>(R.id.toolbarVerticalContainer)
        val prefs = getSharedPreferences("eveditor_ui", MODE_PRIVATE)
        val horizontalKey = "toolbar_horizontal_mode"
        val rightKey = "toolbar_on_right_edge"

        // Five stable semantic groups. The first two actions never change order or group.
        // Existing View instances are moved, so their original listeners and IDs survive.
        val toolbarItems = mutableListOf<View>()
        fun collectToolbarItems(group: ViewGroup) {
            for (i in 0 until group.childCount) {
                val child = group.getChildAt(i)
                if (child is Button || child is CheckBox || child.id == R.id.outputTargetSizeLabel || child.id == R.id.targetSizeMb) toolbarItems.add(child)
                else if (child is ViewGroup) collectToolbarItems(child)
            }
        }
        collectToolbarItems(actionContainer)
        val itemById = toolbarItems.associateBy { it.id }
        actionContainer.removeAllViews()
        val groups = listOf(
            listOf(R.id.openButton, R.id.videoInfoButton, R.id.outputChangesButton, R.id.outputTargetSizeCheck, R.id.outputTargetSizeLabel, R.id.targetSizeMb, R.id.manualOutputNameCheck, R.id.tagMetadataCheck),
            listOf(R.id.mergeButton, R.id.joinAfterButton, R.id.overlayVideoPanelButton, R.id.textPlacementButton, R.id.trackPanelButton),
            listOf(R.id.globalDeleteButton, R.id.outputFormatButton),
            listOf(R.id.imageSceneSearchButton),
            listOf(R.id.colorPanelButton, R.id.vectorButton, R.id.cropButton, R.id.advancedEditButton)
        )
        val groupColors = mapOf(
            R.id.openButton to Color.rgb(144, 202, 249),
            R.id.videoInfoButton to Color.rgb(128, 203, 196),
            R.id.outputChangesButton to Color.rgb(100, 181, 246),
            R.id.mergeButton to Color.rgb(255, 224, 130),
            R.id.globalDeleteButton to Color.rgb(198, 40, 40),
            R.id.joinAfterButton to Color.rgb(255, 202, 90),
            R.id.outputFormatButton to Color.rgb(255, 243, 205),
            R.id.trackPanelButton to Color.rgb(128, 203, 196),
            R.id.overlayVideoPanelButton to Color.rgb(77, 182, 172),
            R.id.imageSceneSearchButton to Color.rgb(225, 190, 231),
            R.id.textPlacementButton to Color.rgb(206, 147, 216),
            R.id.colorPanelButton to Color.rgb(165, 214, 167),
            R.id.vectorButton to Color.rgb(102, 187, 106),
            R.id.cropButton to Color.rgb(77, 182, 172),
            R.id.advancedEditButton to Color.rgb(129, 199, 132)
        )
        for (groupIndex in groups.indices) {
            val group = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                gravity = Gravity.CENTER
                layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.MATCH_PARENT)
            }
            for (itemId in groups[groupIndex]) {
                val item = itemById[itemId] ?: continue
                (item.parent as? ViewGroup)?.removeView(item)
                if (item is Button) {
                    groupColors[itemId]?.let { item.backgroundTintList = android.content.res.ColorStateList.valueOf(it) }
                    item.setPadding(dp(2), dp(2), dp(2), dp(2))
                    item.includeFontPadding = false
                }
                val itemHeight = when (item.id) {
                    R.id.outputTargetSizeLabel -> dp(24)
                    R.id.targetSizeMb -> dp(30)
                    else -> dp(52)
                }
                val compactWidth = when (item.id) {
                    R.id.openButton, R.id.outputChangesButton -> dp(90)
                    R.id.videoInfoButton -> dp(78)
                    R.id.outputTargetSizeCheck -> dp(76)
                    R.id.tagMetadataCheck -> dp(54)
                    R.id.outputTargetSizeLabel -> dp(68)
                    R.id.targetSizeMb -> dp(70)
                    R.id.manualOutputNameCheck -> dp(78)
                    else -> dp(86)
                }
                group.addView(item, LinearLayout.LayoutParams(compactWidth, itemHeight))
            }
            actionContainer.addView(group)
            if (groupIndex < groups.lastIndex) {
                actionContainer.addView(TextView(this).apply {
                    text = "┆┆"
                    setTextColor(Color.rgb(255, 152, 0))
                    textSize = 18f
                    gravity = Gravity.CENTER
                    contentDescription = "toolbar-group-divider"
                }, LinearLayout.LayoutParams(dp(4), ViewGroup.LayoutParams.MATCH_PARENT))
            }
        }
        val toolbarButtons = toolbarItems.filter { it is Button && it !is CheckBox }.map { it as Button }

        fun configureItems(horizontal: Boolean) {
            fun visit(group: ViewGroup, isRoot: Boolean = false) {
                if (group is LinearLayout) {
                    group.orientation = if (horizontal) LinearLayout.HORIZONTAL else LinearLayout.VERTICAL
                    if (!isRoot) {
                        val lp = group.layoutParams as? LinearLayout.LayoutParams
                        if (lp != null) {
                            lp.width = if (horizontal) ViewGroup.LayoutParams.WRAP_CONTENT else ViewGroup.LayoutParams.MATCH_PARENT
                            lp.height = if (horizontal) ViewGroup.LayoutParams.MATCH_PARENT else ViewGroup.LayoutParams.WRAP_CONTENT
                            group.layoutParams = lp
                        }
                    }
                }
                for (i in 0 until group.childCount) {
                    val child = group.getChildAt(i)
                    if (child is ViewGroup) visit(child, false)
                    val lp = child.layoutParams
                    when (child) {
                        is CheckBox -> {
                            val cp = lp as? LinearLayout.LayoutParams ?: continue
                            cp.width = if (horizontal) when (child.id) {
                                R.id.outputTargetSizeCheck -> dp(76)
                                R.id.tagMetadataCheck -> dp(54)
                                R.id.manualOutputNameCheck -> dp(78)
                                else -> dp(86)
                            } else ViewGroup.LayoutParams.MATCH_PARENT
                            cp.height = dp(52)
                            cp.setMargins(0, 0, 0, 0)
                            child.layoutParams = cp
                            child.textSize = if (horizontal) 9.5f else 9f
                            child.gravity = Gravity.CENTER
                        }
                        is Button -> {
                            val bp = lp as? LinearLayout.LayoutParams ?: continue
                            bp.width = if (horizontal) when (child.id) {
                                R.id.openButton, R.id.outputChangesButton -> dp(90)
                                R.id.videoInfoButton -> dp(78)
                                else -> dp(86)
                            } else ViewGroup.LayoutParams.MATCH_PARENT
                            bp.height = dp(52)
                            bp.setMargins(0, 0, 0, 0)
                            child.layoutParams = bp
                            child.textSize = if (horizontal) 9.5f else 9f
                        }
                        is TextView -> {
                            if (child.contentDescription == "toolbar-group-divider") {
                                val dpSize = if (horizontal) dp(12) else dp(12)
                                val tp = lp as? LinearLayout.LayoutParams
                                if (tp != null) {
                                    tp.width = if (horizontal) dpSize else ViewGroup.LayoutParams.MATCH_PARENT
                                    tp.height = if (horizontal) ViewGroup.LayoutParams.MATCH_PARENT else dp(12)
                                    tp.setMargins(0, 0, 0, 0)
                                    child.layoutParams = tp
                                }
                                child.text = if (horizontal) "┆┆" else "═  ═"
                                child.textSize = 18f
                            }
                        }
                        is View -> {
                            if (child !is ViewGroup && child !is TextView) {
                                val vp = lp as? LinearLayout.LayoutParams
                                if (vp != null) {
                                    if (horizontal) {
                                        vp.width = dp(2); vp.height = ViewGroup.LayoutParams.MATCH_PARENT
                                    } else {
                                        vp.width = ViewGroup.LayoutParams.MATCH_PARENT; vp.height = dp(2)
                                    }
                                    child.layoutParams = vp
                                }
                            }
                        }
                    }
                }
            }
            visit(actionContainer, true)
        }

        fun moveContainer(horizontal: Boolean) {
            val oldParent = actionContainer.parent as? ViewGroup
            val target = if (horizontal) horizontalScroll else verticalContainer
            if (oldParent !== target) {
                oldParent?.removeView(actionContainer)
                target.removeAllViews()
                target.addView(actionContainer, if (horizontal) {
                    LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.MATCH_PARENT)
                } else {
                    LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
                })
            }
            configureItems(horizontal)
            horizontalScroll.visibility = if (horizontal) View.VISIBLE else View.GONE
            verticalScroll.visibility = if (horizontal) View.GONE else View.VISIBLE
        }

        fun applyMode(horizontal: Boolean, onRight: Boolean) {
            prefs.edit().putBoolean(horizontalKey, horizontal).putBoolean(rightKey, onRight).apply()
            moveContainer(horizontal)
            root.removeView(rail)
            if (horizontal) {
                root.orientation = LinearLayout.VERTICAL
                val railLp = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(60))
                rail.layoutParams = railLp
                rail.orientation = LinearLayout.HORIZONTAL
                handle.layoutParams = LinearLayout.LayoutParams(dp(64), ViewGroup.LayoutParams.MATCH_PARENT)
                val editorLp = editor.layoutParams as LinearLayout.LayoutParams
                editorLp.width = ViewGroup.LayoutParams.MATCH_PARENT
                editorLp.height = 0
                editorLp.weight = 1f
                editor.layoutParams = editorLp
                root.addView(rail, 0)
                handle.text = "ابزارها  ⋮⋮"
                handle.contentDescription = "برای انتقال ابزارها به نوار عمودی، بکشید به لبه چپ یا راست؛ لمس کوتاه حالت را عوض می‌کند"
            } else {
                root.orientation = LinearLayout.HORIZONTAL
                rail.orientation = LinearLayout.VERTICAL
                rail.layoutParams = LinearLayout.LayoutParams(dp(75), ViewGroup.LayoutParams.MATCH_PARENT)
                handle.layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(38))
                val editorLp = editor.layoutParams as LinearLayout.LayoutParams
                editorLp.width = 0
                editorLp.height = ViewGroup.LayoutParams.MATCH_PARENT
                editorLp.weight = 1f
                editor.layoutParams = editorLp
                val rtl = root.layoutDirection == View.LAYOUT_DIRECTION_RTL
                val index = if (onRight) { if (rtl) 0 else root.childCount } else { if (rtl) root.childCount else 0 }
                root.addView(rail, index.coerceIn(0, root.childCount))
                handle.text = "ابزارها  ⋮⋮  ↔"
                handle.contentDescription = "برای جابه‌جایی نوار ابزار بین لبه چپ و راست بکشید؛ لمس کوتاه نوار افقی را فعال می‌کند"
            }
            rail.translationX = 0f
            rail.translationY = 0f
            root.requestLayout()
            root.post { this@MainActivity.updateToolbarRailHeight() }
        }

        fun findButtonAt(group: ViewGroup, rawX: Float, rawY: Float): Button? {
            for (i in 0 until group.childCount) {
                val child = group.getChildAt(i)
                if (child is Button) {
                    val location = IntArray(2)
                    child.getLocationOnScreen(location)
                    if (rawX >= location[0] && rawX <= location[0] + child.width &&
                        rawY >= location[1] && rawY <= location[1] + child.height) return child
                } else if (child is ViewGroup) {
                    val nested = findButtonAt(child, rawX, rawY)
                    if (nested != null) return nested
                }
            }
            return null
        }
        toolbarButtons.forEach { button ->
            button.setOnLongClickListener {
                val clip = android.content.ClipData.newPlainText("toolbar-button", button.id.toString())
                @Suppress("DEPRECATION")
                button.startDrag(clip, View.DragShadowBuilder(button), button, 0)
                true
            }
        }
        actionContainer.setOnDragListener { _, event ->
            when (event.action) {
                android.view.DragEvent.ACTION_DRAG_STARTED -> event.localState is Button
                android.view.DragEvent.ACTION_DRAG_ENTERED -> true
                android.view.DragEvent.ACTION_DRAG_LOCATION -> true
                android.view.DragEvent.ACTION_DROP -> {
                    val moving = event.localState as? Button ?: return@setOnDragListener false
                    val containerLocation = IntArray(2)
                    actionContainer.getLocationOnScreen(containerLocation)
                    val screenX = containerLocation[0] + event.x
                    val screenY = containerLocation[1] + event.y
                    val target = findButtonAt(actionContainer, screenX, screenY)
                    val targetParent = target?.parent as? ViewGroup
                    val movingParent = moving.parent as? ViewGroup
                    if (movingParent != null) {
                        val oldIndex = movingParent.indexOfChild(moving)
                        val insertAt = if (target != null && targetParent != null) {
                            val targetIndex = targetParent.indexOfChild(target)
                            val loc = IntArray(2); target.getLocationOnScreen(loc)
                            val horizontalNow = prefs.getBoolean(horizontalKey, true)
                            val after = if (horizontalNow) screenX > loc[0] + target.width / 2f else screenY > loc[1] + target.height / 2f
                            targetIndex + if (after) 1 else 0
                        } else (targetParent?.childCount ?: 0)
                        movingParent.removeView(moving)
                        val destination = targetParent ?: (actionContainer.getChildAt(0) as? ViewGroup) ?: return@setOnDragListener false
                        val adjustedInsert = if (movingParent === destination && oldIndex < insertAt) insertAt - 1 else insertAt
                        destination.addView(moving, adjustedInsert.coerceIn(0, destination.childCount))
                        configureItems(prefs.getBoolean(horizontalKey, true))
                        actionContainer.requestLayout()
                    }
                    true
                }
                android.view.DragEvent.ACTION_DRAG_ENDED -> true
                else -> true
            }
        }

        val initialHorizontal = prefs.getBoolean(horizontalKey, true)
        val initialRight = prefs.getBoolean(rightKey, false)
        root.post { applyMode(initialHorizontal, initialRight) }

        var downX = 0f
        var downY = 0f
        var dragging = false
        val slop = android.view.ViewConfiguration.get(this).scaledTouchSlop.toFloat()
        handle.setOnTouchListener { view, event ->
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    downX = event.rawX
                    downY = event.rawY
                    dragging = false
                    true
                }
                MotionEvent.ACTION_MOVE -> {
                    if (kotlin.math.hypot((event.rawX - downX).toDouble(), (event.rawY - downY).toDouble()) > slop) {
                        dragging = true
                        view.alpha = 0.78f
                    }
                    true
                }
                MotionEvent.ACTION_UP -> {
                    view.alpha = 1f
                    if (dragging) {
                        val horizontalMode = prefs.getBoolean(horizontalKey, true)
                        val right = event.rawX >= root.width / 2f
                        // Dragging the top bar's handle toward either screen edge docks it vertically.
                        // In vertical mode the same drag changes the left/right docking edge.
                        applyMode(false, right)
                    } else {
                        applyMode(!prefs.getBoolean(horizontalKey, true), prefs.getBoolean(rightKey, false))
                    }
                    dragging = false
                    true
                }
                MotionEvent.ACTION_CANCEL -> {
                    view.alpha = 1f
                    dragging = false
                    true
                }
                else -> true
            }
        }

        root.addOnLayoutChangeListener { _, _, _, _, _, _, _, _, _ -> this@MainActivity.updateToolbarRailHeight() }
        findViewById<View>(R.id.storyboardTableFrame).addOnLayoutChangeListener { _, _, _, _, _, _, _, _, _ ->
            this@MainActivity.updateToolbarRailHeight()
        }
        findViewById<ScrollView>(R.id.mainScrollView).setOnScrollChangeListener { _, _, _, _, _ ->
            this@MainActivity.updateToolbarRailHeight()
        }
    }

    private fun ensureSingleUndoRedoButtons() {
        val root = findViewById<ViewGroup>(R.id.mainRootLayout)
        val allButtons = mutableListOf<Button>()
        fun collect(view: View) {
            if (view is Button) allButtons.add(view)
            if (view is ViewGroup) {
                for (i in 0 until view.childCount) collect(view.getChildAt(i))
            }
        }
        collect(root)

        fun keepOne(targetId: Int, word: String, arrow: String) {
            val candidates = allButtons.filter { button ->
                button.id == targetId || button.text.toString().contains(word, ignoreCase = true) || button.text.toString().contains(arrow)
            }
            val keeper = candidates.firstOrNull { it.id == targetId } ?: candidates.firstOrNull()
            candidates.forEach { button ->
                if (button !== keeper) (button.parent as? ViewGroup)?.removeView(button)
            }
        }
        keepOne(R.id.undoButton, "undo", "↶")
        keepOne(R.id.redoButton, "redo", "↷")
    }

    private fun saveActiveEdit() {
        if (freeCropMode) {
            readCropOverlay()
            if (!validCropMargins()) return
            cropSettingsSaved = true
            freeCropMode = false
            cropOverlay.visibility = View.GONE
            freeCropControls.visibility = View.GONE
        }
        if (placementMode != PlacementOverlayView.Mode.NONE) {
            placementMode = PlacementOverlayView.Mode.NONE
            placementOverlay.visibility = View.GONE
            if (overlayVideoUri != null) updateOverlayPreviewLayout()
        }
        intArrayOf(
            R.id.fixedColorControls, R.id.textOverlayPanel, R.id.overlayVideoPanel,
            R.id.trackPanel, R.id.timelinePanel, R.id.timelineActionButtons
        ).forEach { findViewById<View>(it)?.visibility = View.GONE }
        statusText.text = "تغییرات فعلی ثبت شد و برای خروجی نهایی آماده است؛ برای ساخت فایل، «خروجی هوشمند» را بزنید"
        Toast.makeText(this, "تغییرات ثبت شد", Toast.LENGTH_SHORT).show()
    }

    private fun cancelActiveEdit() {
        val hadPlacement = placementMode != PlacementOverlayView.Mode.NONE
        val hadCrop = freeCropMode
        val hadActivePanel = intArrayOf(
            R.id.fixedColorControls, R.id.textOverlayPanel, R.id.overlayVideoPanel,
            R.id.trackPanel, R.id.timelinePanel, R.id.timelineActionButtons
        ).any { findViewById<View>(it)?.visibility == View.VISIBLE }
        if (hadPlacement || hadCrop || hadActivePanel) {
            if (undoHistory.isNotEmpty()) undoEditorStep()
        }
        placementMode = PlacementOverlayView.Mode.NONE
        placementOverlay.visibility = View.GONE
        freeCropMode = false
        cropOverlay.visibility = View.GONE
        freeCropControls.visibility = View.GONE
        intArrayOf(
            R.id.fixedColorControls, R.id.textOverlayPanel, R.id.overlayVideoPanel,
            R.id.trackPanel, R.id.timelinePanel, R.id.timelineActionButtons
        ).forEach { findViewById<View>(it)?.visibility = View.GONE }
        findViewById<EditText>(R.id.overlayTextInput).clearFocus()
        statusText.text = "حالت ویرایش جاری بسته شد؛ تغییرات تأییدنشدهٔ ابزارهای تعاملی لغو شدند"
        Toast.makeText(this, "ویرایش جاری لغو شد", Toast.LENGTH_SHORT).show()
    }

    private fun recordUndoState() {
        if (restoringHistory) return
        undoHistory.addLast(captureEditorHistoryState())
        while (undoHistory.size > maxHistorySteps) undoHistory.removeFirst()
        redoHistory.clear(); updateHistoryButtons()
    }

    private fun restoreEditorHistoryState(state: EditorHistoryState) {
        restoringHistory = true
        try {
            timelineSplitPoints.clear(); timelineSplitPoints.addAll(state.splitPoints)
            deletedTimelineRanges.clear(); deletedTimelineRanges.addAll(state.deletedRanges)
            trackClips.clear(); trackClips.addAll(state.clips)
            frameColorProfiles.clear(); frameColorProfiles.putAll(state.profiles)
            cropLeftPct=state.crop[0]; cropTopPct=state.crop[1]; cropRightPct=state.crop[2]; cropBottomPct=state.crop[3]; cropSettingsSaved=state.cropSaved
            autoColorEnabled=state.autoColor; overlayVideoUri=state.overlayUri
            findViewById<EditText>(R.id.overlayTextInput).setText(state.text)
            textXPercent=state.textX; textYPercent=state.textY; liveTextSize=state.textSize
            overlayVideoXPercent=state.overlayX; overlayVideoYPercent=state.overlayY; overlayVideoWidthPercent=state.overlayWidth
            mergeUris.clear(); mergeUris.addAll(state.merge); vectorUris.clear(); vectorUris.addAll(state.vector); referenceImageUri=state.reference
            selectedTrackClipId=null; selectedTimelineRange=null
            timelineView.setTimeline(videoDurationMs, timelineSplitPoints.toList(), deletedTimelineRanges)
            trackTimelineView.setClips(trackClips.toList(), videoDurationMs); syncLegacyTrackUris()
            findViewById<Button>(R.id.autoColorButton).text=if(autoColorEnabled) "Auto Color: روشن" else "Auto Color"
            findViewById<Button>(R.id.pickOverlayVideoButton).text=if(overlayVideoUri!=null) "ویدیوی رویی انتخاب شد ✓" else "انتخاب ویدیوی رویی"
            findViewById<Button>(R.id.mergeButton).text=if(mergeUris.isEmpty()) "Merge • چند ویدیو" else "Merge • ${mergeUris.size} ویدیو ✓"
            refreshSelectionStyles(); updateSelectionText(); updateOverlayPreviewLayout()
            statusText.text="مرحلهٔ ویرایش بازگردانی شد؛ فایل اصلی ویدیو تغییری نکرده است"
        } finally { restoringHistory=false }
        updateHistoryButtons()
    }

    private fun undoEditorStep() {
        if (undoHistory.isEmpty()) { Toast.makeText(this, "مرحله‌ای برای Undo وجود ندارد", Toast.LENGTH_SHORT).show(); return }
        redoHistory.addLast(captureEditorHistoryState()); restoreEditorHistoryState(undoHistory.removeLast()); statusText.text="Undo انجام شد"
    }

    private fun redoEditorStep() {
        if (redoHistory.isEmpty()) { Toast.makeText(this, "مرحله‌ای برای Redo وجود ندارد", Toast.LENGTH_SHORT).show(); return }
        undoHistory.addLast(captureEditorHistoryState()); restoreEditorHistoryState(redoHistory.removeLast()); statusText.text="Redo انجام شد"
    }

    private fun updateHistoryButtons() {
        findViewById<Button>(R.id.undoButton).apply { isEnabled=undoHistory.isNotEmpty(); alpha=if(isEnabled) 1f else 0.55f }
        findViewById<Button>(R.id.redoButton).apply { isEnabled=redoHistory.isNotEmpty(); alpha=if(isEnabled) 1f else 0.55f }
    }

    private fun splitSelectedTrackClip() {
        val selectedId = selectedTrackClipId ?: run { Toast.makeText(this, "ابتدا یک قطعه از ترک‌ها را انتخاب کنید", Toast.LENGTH_SHORT).show(); return }
        val clip = trackClips.firstOrNull { it.id == selectedId } ?: return
        val playhead = try { videoView.currentPosition.toLong() } catch (_: Exception) { timelineView.playheadMs }
        val offset = playhead - clip.startMs
        if (offset < 500L || offset > clip.durationMs - 500L) {
            Toast.makeText(this, "نشانگر پخش باید داخل قطعه و دست‌کم نیم ثانیه دور از لبه‌ها باشد", Toast.LENGTH_LONG).show(); return
        }
        val index = trackClips.indexOfFirst { it.id == selectedId }
        recordUndoState()
        val first = clip.copy(durationMs = offset)
        val second = clip.copy(id = nextTrackClipId++, name = clip.name + " (بخش ۲)", startMs = clip.startMs + offset,
            sourceStartMs = clip.sourceStartMs + offset, durationMs = clip.durationMs - offset)
        trackClips[index] = first
        trackClips.add(index + 1, second)
        selectedTrackClipId = second.id
        trackTimelineView.setClips(trackClips.toList(), videoDurationMs)
        trackTimelineView.selectClip(second.id)
        statusText.text = "ترک به دو بخش جدا تقسیم شد؛ هر بخش را مستقل می‌توانید جابه‌جا یا کوتاه کنید."
    }

    /** Delete currently selected items directly; only show the legacy options when nothing is selected. */
    private fun deleteSelectionOrShowOptions() {
        val trackIds = trackTimelineView.selectedClipIds.toSet()
        val hasSelection = selectedFrames.isNotEmpty() || trackIds.isNotEmpty() || selectedTrackClipId != null || selectedTimelineRange != null
        if (!hasSelection) {
            Toast.makeText(this, "ابتدا موردی را در همان بخش انتخاب کنید؛ برای انتخاب چند ترک، هر ترک را نگه دارید", Toast.LENGTH_LONG).show()
            return
        }
        var removed = 0
        if (selectedFrames.isNotEmpty()) {
            val count = selectedFrames.size
            deleteSelectedStoryboardFrames()
            removed += count
        }
        val idsToRemove = if (trackIds.isNotEmpty()) trackIds else setOfNotNull(selectedTrackClipId)
        if (idsToRemove.isNotEmpty()) {
            val before = trackClips.size
            trackClips.removeAll { it.id in idsToRemove }
            removed += before - trackClips.size
            selectedTrackClipId = null
            trackTimelineView.clearSelection()
            trackTimelineView.setClips(trackClips.toList(), videoDurationMs)
            syncLegacyTrackUris()
            findViewById<Button>(R.id.addAudioButton).text = if (trackClips.any { it.kind == TrackClipKind.AUDIO }) "صداها (${trackClips.count { it.kind == TrackClipKind.AUDIO }}) ✓" else "افزودن صدا"
            findViewById<Button>(R.id.addSubtitleButton).text = if (trackClips.any { it.kind == TrackClipKind.SUBTITLE }) "زیرنویس‌ها (${trackClips.count { it.kind == TrackClipKind.SUBTITLE }}) ✓" else "افزودن زیرنویس"
            findViewById<Button>(R.id.addVideoTrackButton).text = if (trackClips.any { it.kind == TrackClipKind.VIDEO }) "ویدیوها (${trackClips.count { it.kind == TrackClipKind.VIDEO }}) ✓" else "افزودن ویدیو"
        }
        selectedTimelineRange?.let { range ->
            if (deletedTimelineRanges.none { it.first == range.first && it.second == range.second }) deletedTimelineRanges.add(range)
            selectedTimelineRange = null
            timelineView.setTimeline(videoDurationMs, timelineSplitPoints.toList(), deletedTimelineRanges)
            removed++
        }
        if (removed == 0) Toast.makeText(this, "مورد انتخاب‌شده‌ای برای حذف وجود ندارد", Toast.LENGTH_SHORT).show()
        else statusText.text = "$removed مورد انتخاب‌شده برای حذف/حذف از خروجی اعمال شد"
    }

    /** A central Delete menu for removable items across the main editor sections. */
    private fun showGlobalDeleteDialog() {
        val actions = mutableListOf<Pair<String, () -> Unit>>()
        if (selectedFrames.isNotEmpty()) actions += "اسلایدهای انتخاب‌شده (${selectedFrames.size})" to { deleteSelectedStoryboardFrames() }
        if (selectedTrackClipId != null && trackClips.any { it.id == selectedTrackClipId }) actions += "قطعهٔ انتخاب‌شده از ترک‌ها" to { deleteSelectedTrackClip() }
        if (selectedTimelineRange != null) actions += "قطعهٔ انتخاب‌شده از نوار زمان" to {
            val range = selectedTimelineRange
            if (range != null) {
                if (deletedTimelineRanges.none { it.first == range.first && it.second == range.second }) deletedTimelineRanges.add(range)
                selectedTimelineRange = null
                timelineView.setTimeline(videoDurationMs, timelineSplitPoints.toList(), deletedTimelineRanges)
                trackTimelineView.setClips(trackClips.toList(), videoDurationMs)
                statusText.text = "قطعهٔ انتخاب‌شده برای حذف از خروجی علامت خورد"
            }
        }
        if (selectedFrames.any { frameColorProfiles.containsKey(it) }) actions += "تنظیم رنگ اسلایدهای انتخاب‌شده" to {
            selectedFrames.forEach { frameColorProfiles.remove(it) }
            refreshSelectionStyles()
            statusText.text = "تنظیم رنگ اسلایدهای انتخاب‌شده پاک شد"
        }
        if (overlayVideoUri != null) actions += "ویدیوی رویی" to {
            overlayVideoUri = null
            releaseOverlayPreviewPlayer()
            findViewById<Button>(R.id.pickOverlayVideoButton).text = "انتخاب ویدیوی رویی"
            placementMode = PlacementOverlayView.Mode.NONE
            placementOverlay.visibility = View.GONE
            statusText.text = "ویدیوی رویی حذف شد"
        }
        if (findViewById<EditText>(R.id.overlayTextInput).text.isNotBlank()) actions += "متن رویی" to {
            findViewById<EditText>(R.id.overlayTextInput).text.clear()
            statusText.text = "متن رویی پاک شد"
        }
        if (mergeUris.isNotEmpty()) actions += "فهرست ویدیوهای Merge/Join" to {
            mergeUris.clear()
            findViewById<Button>(R.id.mergeButton).text = "Merge • چند ویدیو"
            statusText.text = "فهرست ویدیوهای Merge/Join پاک شد"
        }
        if (referenceImageUri != null) actions += "عکس مرجع جست‌وجوی صحنه" to {
            referenceImageUri = null
            statusText.text = "عکس مرجع پاک شد"
        }
        if (vectorUris.isNotEmpty()) actions += "فهرست ویدیوهای Vector" to {
            vectorUris.clear()
            statusText.text = "فهرست ویدیوهای Vector پاک شد"
        }
        if (cropSettingsSaved || cropLeftPct != 0 || cropTopPct != 0 || cropRightPct != 0 || cropBottomPct != 0) actions += "تنظیمات Free Crop" to {
            cropLeftPct = 0; cropTopPct = 0; cropRightPct = 0; cropBottomPct = 0
            cropSettingsSaved = false; freeCropMode = false
            cropOverlay.visibility = View.GONE; freeCropControls.visibility = View.GONE
            statusText.text = "تنظیمات Free Crop پاک شد"
        }
        if (timelineSplitPoints.isNotEmpty() || deletedTimelineRanges.isNotEmpty()) actions += "همهٔ برش‌ها و حذف‌های نوار زمان" to {
            timelineSplitPoints.clear(); deletedTimelineRanges.clear(); selectedTimelineRange = null
            timelineView.setTimeline(videoDurationMs, emptyList(), emptyList())
            statusText.text = "برش‌ها و حذف‌های نوار زمان پاک شدند"
        }
        if (actions.isEmpty()) {
            Toast.makeText(this, "مورد قابل‌حذفی انتخاب نشده است؛ ابتدا یک اسلاید، قطعه یا مورد را انتخاب کنید", Toast.LENGTH_LONG).show()
            return
        }
        val labels = actions.map { it.first }.toTypedArray()
        val dialog = AlertDialog.Builder(this)
            .setTitle("Delete • حذف عمومی")
            .setItems(labels) { dialog, which ->
                actions[which].second.invoke()
                dialog.dismiss()
            }
            .setNegativeButton("انصراف", null)
            .create()
        dialog.setOnShowListener { standardizeDialogButtons(dialog) }
        dialog.show()
    }

    private fun deleteSelectedTrackClip() {
        val id = selectedTrackClipId ?: run { Toast.makeText(this, "ابتدا یک قطعهٔ ترک را انتخاب کنید", Toast.LENGTH_SHORT).show(); return }
        recordUndoState()
        trackClips.removeAll { it.id == id }
        selectedTrackClipId = null
        trackTimelineView.setClips(trackClips.toList(), videoDurationMs)
        syncLegacyTrackUris()
        findViewById<Button>(R.id.addAudioButton).text = if (trackClips.any { it.kind == TrackClipKind.AUDIO }) "صداها (${trackClips.count { it.kind == TrackClipKind.AUDIO }}) ✓" else "افزودن صدا"
        findViewById<Button>(R.id.addSubtitleButton).text = if (trackClips.any { it.kind == TrackClipKind.SUBTITLE }) "زیرنویس‌ها (${trackClips.count { it.kind == TrackClipKind.SUBTITLE }}) ✓" else "افزودن زیرنویس"
        findViewById<Button>(R.id.addVideoTrackButton).text = if (trackClips.any { it.kind == TrackClipKind.VIDEO }) "ویدیوها (${trackClips.count { it.kind == TrackClipKind.VIDEO }}) ✓" else "افزودن ویدیو"
        statusText.text = "قطعهٔ انتخاب‌شده حذف شد"
    }

    private fun chooseExternalAudio() {
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE)
            type = "audio/*"
            putExtra(Intent.EXTRA_ALLOW_MULTIPLE, true)
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        }
        try { startActivityForResult(intent, PICK_EXTERNAL_AUDIO) }
        catch (_: Exception) { Toast.makeText(this, "انتخاب‌گر فایل صوتی در دسترس نیست", Toast.LENGTH_LONG).show() }
    }

    private fun chooseVideoForTrack() {
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE)
            type = "video/*"
            putExtra(Intent.EXTRA_ALLOW_MULTIPLE, true)
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        }
        try { startActivityForResult(intent, PICK_TRACK_VIDEO) }
        catch (_: Exception) { Toast.makeText(this, "انتخاب‌گر ویدیو در دسترس نیست", Toast.LENGTH_LONG).show() }
    }

    private fun chooseExternalSubtitle() {
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE)
            type = "*/*"
            putExtra(Intent.EXTRA_MIME_TYPES, arrayOf("application/x-subrip", "text/plain", "text/vtt", "application/x-ass", "application/x-ssa", "application/octet-stream"))
            putExtra(Intent.EXTRA_ALLOW_MULTIPLE, true)
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        }
        try { startActivityForResult(intent, PICK_EXTERNAL_SUBTITLE) }
        catch (_: Exception) { Toast.makeText(this, "انتخاب‌گر زیرنویس در دسترس نیست", Toast.LENGTH_LONG).show() }
    }

    private fun displayNameForUri(uri: Uri): String {
        var name: String? = null
        contentResolver.query(uri, arrayOf(OpenableColumns.DISPLAY_NAME), null, null, null)?.use { cursor ->
            if (cursor.moveToFirst()) name = cursor.getString(0)
        }
        return name ?: (uri.lastPathSegment ?: "track")
    }

    private fun copyUriToCache(uri: Uri, prefix: String): File {
        val displayName = displayNameForUri(uri)
        val extension = displayName.substringAfterLast('.', "bin").lowercase(java.util.Locale.ROOT)
            .filter { it.isLetterOrDigit() }.take(8).ifBlank { "bin" }
        val destination = File(cacheDir, "${prefix}_${System.currentTimeMillis()}.$extension")
        contentResolver.openInputStream(uri)?.use { input -> destination.outputStream().use { output -> input.copyTo(output) } }
            ?: throw IllegalStateException("خواندن فایل انتخاب‌شده ممکن نشد")
        if (destination.length() == 0L) {
            destination.delete()
            throw IllegalStateException("فایل انتخاب‌شده خالی است")
        }
        return destination
    }

    /** Composite independent VIDEO overlays and mix positioned audio/subtitle clips from the track timeline. */
    private fun exportTrackTimeline() {
        val sourceUri = selectedUri ?: run { Toast.makeText(this, "ابتدا ویدیوی اصلی را انتخاب کنید", Toast.LENGTH_LONG).show(); return }
        val clips = trackClips.toList().filter { it.durationMs > 0L }
        if (clips.isEmpty()) return
        val button = findViewById<Button>(R.id.outputChangesButton)
        button.isEnabled = false
        val videoClips = clips.filter { it.kind == TrackClipKind.VIDEO }
        statusText.text = if (videoClips.isNotEmpty()) {
            "در حال ترکیب ${videoClips.size} ویدیوی ترک با ویدیوی اصلی؛ ممکن است رمزگذاری تصویر زمان ببرد…"
        } else "در حال ساخت خروجی از نوار ترک‌ها؛ کدک تصویر اصلی حفظ می‌شود…"
        worker.execute {
            val tempFiles = mutableListOf<File>()
            var output: File? = null
            var error: String? = null
            try {
                val sourceFile = copyUriToCache(sourceUri, "evc_tracks_source")
                tempFiles.add(sourceFile)
                val audioClips = clips.filter { it.kind == TrackClipKind.AUDIO }
                val subtitleClips = clips.filter { it.kind == TrackClipKind.SUBTITLE }
                val audioFiles = audioClips.map { clip -> copyUriToCache(clip.uri, "evc_timeline_audio").also { tempFiles.add(it) } }
                val videoFiles = videoClips.map { clip -> copyUriToCache(clip.uri, "evc_timeline_video").also { tempFiles.add(it) } }
                val subtitleFiles = subtitleClips.map { clip -> copyUriToCache(clip.uri, "evc_timeline_subtitle").also { tempFiles.add(it) } }
                val outputFile = File(cacheDir, "evc_timeline_tracks_${System.currentTimeMillis()}.${outputExtension()}")
                output = outputFile

                val args = mutableListOf("-y", "-i", sourceFile.absolutePath)
                // Keep input indexes deterministic: main, audio clips, video clips, subtitle clips.
                audioFiles.forEach { args.addAll(listOf("-i", it.absolutePath)) }
                videoFiles.forEach { args.addAll(listOf("-i", it.absolutePath)) }
                val subtitleInputIndexes = mutableListOf<Int>()
                subtitleFiles.forEachIndexed { index, file ->
                    val clip = subtitleClips[index]
                    args.addAll(listOf("-itsoffset", String.format(java.util.Locale.US, "%.3f", clip.startMs / 1000.0),
                        "-ss", String.format(java.util.Locale.US, "%.3f", clip.sourceStartMs / 1000.0),
                        "-t", String.format(java.util.Locale.US, "%.3f", clip.durationMs / 1000.0), "-i", file.absolutePath))
                    subtitleInputIndexes.add(1 + audioFiles.size + videoFiles.size + index)
                }

                fun hasAudio(file: File): Boolean {
                    return try {
                        val extractor = MediaExtractor()
                        extractor.setDataSource(file.absolutePath)
                        val found = (0 until extractor.trackCount).any {
                            extractor.getTrackFormat(it).getString(MediaFormat.KEY_MIME)?.startsWith("audio/") == true
                        }
                        extractor.release()
                        found
                    } catch (_: Exception) { false }
                }
                val sourceHasAudio = hasAudio(sourceFile)
                val videoHasAudio = videoFiles.map { hasAudio(it) }
                val mainVideoSize = try {
                    val retriever = MediaMetadataRetriever()
                    retriever.setDataSource(sourceFile.absolutePath)
                    val width = retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_VIDEO_WIDTH)?.toIntOrNull()?.coerceAtLeast(16) ?: 1280
                    val height = retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_VIDEO_HEIGHT)?.toIntOrNull()?.coerceAtLeast(16) ?: 720
                    retriever.release()
                    width to height
                } catch (_: Exception) { 1280 to 720 }
                val overlayMaxWidth = (mainVideoSize.first * 0.34f).toInt().coerceAtLeast(96)
                val overlayMaxHeight = (mainVideoSize.second * 0.34f).toInt().coerceAtLeast(96)

                val filterParts = mutableListOf<String>()
                var currentVideoLabel = "0:v:0"
                if (videoClips.isNotEmpty()) {
                    filterParts.add("[0:v:0]setpts=PTS-STARTPTS[evc_vbase0]")
                    currentVideoLabel = "evc_vbase0"
                    val mainInputIndex = 1 + audioFiles.size
                    videoClips.forEachIndexed { index, clip ->
                        val inputIndex = mainInputIndex + index
                        val sourceStart = String.format(java.util.Locale.US, "%.3f", clip.sourceStartMs / 1000.0)
                        val duration = String.format(java.util.Locale.US, "%.3f", clip.durationMs / 1000.0)
                        val start = String.format(java.util.Locale.US, "%.3f", clip.startMs / 1000.0)
                        val end = String.format(java.util.Locale.US, "%.3f", (clip.startMs + clip.durationMs) / 1000.0)
                        val clipLabel = "evc_vclip$index"
                        val nextLabel = "evc_vbase${index + 1}"
                        // Each independent VIDEO clip is fitted inside a compact overlay tile.
                        // Four corner positions are cycled for simultaneous clips; later clips
                        // remain visible rather than replacing the main picture.
                        filterParts.add("[$inputIndex:v:0]trim=start=$sourceStart:duration=$duration,setpts=PTS-STARTPTS+${start}/TB,scale=w=$overlayMaxWidth:h=$overlayMaxHeight:force_original_aspect_ratio=decrease,setsar=1[$clipLabel]")
                        val x = when (index % 4) { 0, 2 -> "main_w-overlay_w-24"; else -> "24" }
                        val y = when (index % 4) { 0, 1 -> "24"; else -> "main_h-overlay_h-24" }
                        filterParts.add("[$currentVideoLabel][$clipLabel]overlay=x='$x':y='$y':eof_action=pass:shortest=0:repeatlast=0:enable='between(t,$start,$end)'[$nextLabel]")
                        currentVideoLabel = nextLabel
                    }
                }

                val audioInputs = mutableListOf<String>()
                if (sourceHasAudio) {
                    filterParts.add("[0:a:0]asetpts=PTS-STARTPTS,volume=1[evc_orig]")
                    audioInputs.add("[evc_orig]")
                }
                audioClips.forEachIndexed { index, clip ->
                    val inputIndex = 1 + index
                    val sourceStart = String.format(java.util.Locale.US, "%.3f", clip.sourceStartMs / 1000.0)
                    val duration = String.format(java.util.Locale.US, "%.3f", clip.durationMs / 1000.0)
                    val delay = clip.startMs.coerceAtLeast(0L)
                    filterParts.add("[$inputIndex:a:0]atrim=start=$sourceStart:duration=$duration,asetpts=PTS-STARTPTS,adelay=${delay}|${delay}[evc_a$index]")
                    audioInputs.add("[evc_a$index]")
                }
                videoClips.forEachIndexed { index, clip ->
                    if (videoHasAudio[index]) {
                        val inputIndex = 1 + audioFiles.size + index
                        val sourceStart = String.format(java.util.Locale.US, "%.3f", clip.sourceStartMs / 1000.0)
                        val duration = String.format(java.util.Locale.US, "%.3f", clip.durationMs / 1000.0)
                        val delay = clip.startMs.coerceAtLeast(0L)
                        filterParts.add("[$inputIndex:a:0]atrim=start=$sourceStart:duration=$duration,asetpts=PTS-STARTPTS,adelay=${delay}|${delay}[evc_va$index]")
                        audioInputs.add("[evc_va$index]")
                    }
                }
                val hasMixedAudio = audioInputs.isNotEmpty()
                if (hasMixedAudio) {
                    filterParts.add(audioInputs.joinToString("") + "amix=inputs=${audioInputs.size}:duration=longest:dropout_transition=0[evc_mix]")
                }

                if (videoClips.isNotEmpty()) {
                    args.addAll(listOf("-filter_complex", filterParts.joinToString(";"), "-map", "[$currentVideoLabel]"))
                    if (hasMixedAudio) args.addAll(listOf("-map", "[evc_mix]"))
                    else if (sourceHasAudio) args.addAll(listOf("-map", "0:a?"))
                    args.addAll(listOf("-c:v", "mpeg4", "-q:v", "3", "-pix_fmt", "yuv420p"))
                    if (hasMixedAudio) args.addAll(listOf("-c:a", "aac", "-b:a", "192k"))
                    else if (sourceHasAudio) args.addAll(listOf("-c:a", "copy"))
                    else args.add("-an")
                } else if (hasMixedAudio) {
                    args.addAll(listOf("-filter_complex", filterParts.joinToString(";"), "-map", "0:v:0", "-map", "[evc_mix]", "-c:v", "copy", "-c:a", "aac", "-b:a", "192k"))
                } else {
                    args.addAll(listOf("-map", "0:v:0", "-map", "0:a?", "-c:v", "copy", "-c:a", "copy"))
                }
                subtitleInputIndexes.forEach { index -> args.addAll(listOf("-map", "$index:s:0")) }
                if (subtitleInputIndexes.isNotEmpty()) args.addAll(listOf("-c:s", if (outputContainerMatroska) "copy" else "mov_text"))
                if (!outputContainerMatroska) args.addAll(listOf("-movflags", "+faststart"))
                args.addAll(listOf("-max_muxing_queue_size", "2048", "-f", if (outputContainerMatroska) "matroska" else "mp4"))
                if (videoDurationMs > 0L) args.addAll(listOf("-t", String.format(java.util.Locale.US, "%.3f", videoDurationMs / 1000.0)))
                args.add(outputFile.absolutePath)
                val session = FFmpegKit.executeWithArguments(args.toTypedArray())
                if (!ReturnCode.isSuccess(session.returnCode) || !outputFile.exists() || outputFile.length() == 0L) {
                    throw IllegalStateException("ساخت خروجی ترک‌ها ناموفق بود: ${session.allLogsAsString.takeLast(1800)}")
                }
            } catch (e: Exception) {
                error = e.message ?: e.javaClass.simpleName
                output?.delete(); output = null
            } finally { tempFiles.forEach { it.delete() } }
            mainHandler.post {
                button.isEnabled = true
                val result = output
                if (result == null || !result.exists() || result.length() == 0L) {
                    statusText.text = "خروجی ترک‌ها ناموفق بود: ${error ?: "خطای ناشناخته"}"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show(); result?.delete(); return@post
                }
                try {
                    val ext = outputExtension()
                    val values = ContentValues().apply {
                        put(MediaStore.Video.Media.DISPLAY_NAME, requestedOutputDisplayName("EVC_Timeline_${System.currentTimeMillis()}", ext))
                        put(MediaStore.Video.Media.MIME_TYPE, outputMimeType())
                        if (android.os.Build.VERSION.SDK_INT >= 29) { put(MediaStore.Video.Media.RELATIVE_PATH, Environment.DIRECTORY_MOVIES + "/EVC"); put(MediaStore.Video.Media.IS_PENDING, 1) }
                    }
                    val uri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values) ?: throw IllegalStateException("ساخت فایل در Movies/EVC ناموفق بود")
                    contentResolver.openOutputStream(uri)?.use { out -> FileInputStream(result).use { it.copyTo(out) } } ?: throw IllegalStateException("نوشتن خروجی ناموفق بود")
                    if (android.os.Build.VERSION.SDK_INT >= 29) contentResolver.update(uri, ContentValues().apply { put(MediaStore.Video.Media.IS_PENDING, 0) }, null, null)
                    result.delete()
                    restoreNormalStoryboardAfterExport()
                    statusText.text = if (videoClips.isNotEmpty()) {
                        "خروجی چندویدیویی در Movies/EVC ذخیره شد؛ ویدیوهای ترک VIDEO به‌صورت لایه‌های کوچک روی تصویر اصلی ترکیب شدند و صداهای موجود با هم میکس شدند."
                    } else "خروجی نوار ترک‌ها در Movies/EVC ذخیره شد؛ کدک ویدیوی اصلی بدون رمزگذاری مجدد حفظ شد. صداهای افزوده‌شده با صدای اصلی ترکیب شدند."
                    Toast.makeText(this, "خروجی نوار ترک‌ها ذخیره شد", Toast.LENGTH_LONG).show()
                } catch (e: Exception) { result.delete(); statusText.text = "ذخیره خروجی ناموفق بود: ${e.message}"; Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show() }
            }
        }
    }

    private fun exportWithExternalTracks() {
        val sourceUri = selectedUri
        val audioUri = externalAudioUri
        val subtitleUri = externalSubtitleUri
        if (sourceUri == null) {
            Toast.makeText(this, "ابتدا ویدیوی اصلی را انتخاب کنید", Toast.LENGTH_LONG).show()
            return
        }
        if (audioUri == null && subtitleUri == null) {
            Toast.makeText(this, "ابتدا با دکمه‌های «افزودن صدا» یا «افزودن زیرنویس» یک فایل انتخاب کنید", Toast.LENGTH_LONG).show()
            return
        }
        // Android supports reliable multi-track MP4 muxing through MediaMuxer starting
        // with API 26. On API 24-25, avoid invoking the native multi-track muxer because
        // adding a second audio track is not consistently supported; keep the established
        // FFmpeg path for those devices instead.
        if (audioUri != null && subtitleUri == null && !outputContainerMatroska &&
            android.os.Build.VERSION.SDK_INT >= 26) {
            exportAdditionalAudioTrackWithMediaMuxer(sourceUri, audioUri)
            return
        }
        val button = findViewById<Button>(R.id.outputChangesButton)
        button.isEnabled = false
        findViewById<Button>(R.id.addAudioButton).isEnabled = false
        findViewById<Button>(R.id.addSubtitleButton).isEnabled = false
        statusText.text = "در حال افزودن ترک‌های صوتی/زیرنویس بدون رمزگذاری مجدد ویدیو…"
        worker.execute {
            var sourceFile: File? = null
            var audioFile: File? = null
            var subtitleFile: File? = null
            var output: File? = null
            var error: String? = null
            try {
                val videoInputFile = copyUriToCache(sourceUri, "evc_track_video")
                sourceFile = videoInputFile
                val selectedAudioFile = if (audioUri != null) copyUriToCache(audioUri, "evc_track_audio") else null
                audioFile = selectedAudioFile
                val selectedSubtitleFile = if (subtitleUri != null) copyUriToCache(subtitleUri, "evc_track_subtitle") else null
                subtitleFile = selectedSubtitleFile
                val outputFile = File(cacheDir, "evc_tracks_${System.currentTimeMillis()}.${outputExtension()}")
                output = outputFile
                val args = mutableListOf("-y", "-i", videoInputFile.absolutePath)
                var audioInputIndex: Int? = null
                var subtitleInputIndex: Int? = null
                if (selectedAudioFile != null) {
                    audioInputIndex = 1
                    args.addAll(listOf("-i", selectedAudioFile.absolutePath))
                }
                if (selectedSubtitleFile != null) {
                    subtitleInputIndex = if (selectedAudioFile != null) 2 else 1
                    args.addAll(listOf("-i", selectedSubtitleFile.absolutePath))
                }
                args.addAll(listOf("-map", "0:v:0", "-map", "0:a?"))
                if (audioInputIndex != null) args.addAll(listOf("-map", "$audioInputIndex:a:0"))
                if (subtitleInputIndex != null) args.addAll(listOf("-map", "$subtitleInputIndex:s:0"))
                args.addAll(listOf("-c:v", "copy", "-c:a", "copy"))
                if (subtitleInputIndex != null) {
                    if (outputContainerMatroska) args.addAll(listOf("-c:s", "copy"))
                    else args.addAll(listOf("-c:s", "mov_text"))
                }
                args.addAll(listOf("-max_muxing_queue_size", "2048", "-f", if (outputContainerMatroska) "matroska" else "mp4", outputFile.absolutePath))
                val session = FFmpegKit.executeWithArguments(args.toTypedArray())
                if (!ReturnCode.isSuccess(session.returnCode) || !outputFile.exists() || outputFile.length() == 0L) {
                    throw IllegalStateException("ساخت خروجی ناموفق بود: ${session.allLogsAsString.takeLast(1200)}")
                }
            } catch (e: Exception) {
                error = e.message ?: e.javaClass.simpleName
                output?.delete()
                output = null
            } finally {
                sourceFile?.delete()
                audioFile?.delete()
                subtitleFile?.delete()
            }
            mainHandler.post {
                button.isEnabled = true
                findViewById<Button>(R.id.addAudioButton).isEnabled = true
                findViewById<Button>(R.id.addSubtitleButton).isEnabled = true
                val result = output
                if (result == null || !result.exists() || result.length() == 0L) {
                    statusText.text = "افزودن صدا/زیرنویس ناموفق بود: ${error ?: "خطای ناشناخته"}"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                    result?.delete()
                    return@post
                }
                try {
                    val ext = outputExtension()
                    val values = ContentValues().apply {
                        put(MediaStore.Video.Media.DISPLAY_NAME, requestedOutputDisplayName("EVC_tracks_${System.currentTimeMillis()}", ext))
                        put(MediaStore.Video.Media.MIME_TYPE, outputMimeType())
                        if (android.os.Build.VERSION.SDK_INT >= 29) {
                            put(MediaStore.Video.Media.RELATIVE_PATH, Environment.DIRECTORY_MOVIES + "/EVC")
                            put(MediaStore.Video.Media.IS_PENDING, 1)
                        }
                    }
                    val outUri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
                        ?: throw IllegalStateException("ساخت فایل در Movies/EVC ممکن نشد")
                    contentResolver.openOutputStream(outUri)?.use { stream -> FileInputStream(result).use { it.copyTo(stream) } }
                        ?: throw IllegalStateException("نوشتن فایل خروجی ناموفق بود")
                    if (android.os.Build.VERSION.SDK_INT >= 29) {
                        contentResolver.update(outUri, ContentValues().apply { put(MediaStore.Video.Media.IS_PENDING, 0) }, null, null)
                    }
                    result.delete()
                    restoreNormalStoryboardAfterExport()
                    statusText.text = "خروجی همراه ترک‌های انتخابی در Movies/EVC ذخیره شد؛ ویدیو بدون رمزگذاری مجدد کپی شد"
                    Toast.makeText(this, "خروجی در پوشهٔ Movies/EVC ذخیره شد", Toast.LENGTH_LONG).show()
                } catch (e: Exception) {
                    result.delete()
                    statusText.text = "ذخیرهٔ خروجی ناموفق بود: ${e.message ?: "خطا"}"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                }
            }
        }
    }

    /**
     * Adds a selected audio file as an additional MP4 audio track using Android's native muxer.
     * The source video/audio samples are copied unchanged. This route is used only when no
     * subtitle track is requested and the selected output container is MP4.
     */
    private fun exportAdditionalAudioTrackWithMediaMuxer(sourceUri: Uri, audioUri: Uri) {
        val button = findViewById<Button>(R.id.outputChangesButton)
        button.isEnabled = false
        findViewById<Button>(R.id.addAudioButton).isEnabled = false
        findViewById<Button>(R.id.addSubtitleButton).isEnabled = false
        statusText.text = "در حال افزودن ترک صوتی با موتور داخلی اندروید؛ ویدیو دوباره رمزگذاری نمی‌شود…"
        worker.execute {
            var sourceFile: File? = null
            var audioFile: File? = null
            var output: File? = null
            var error: String? = null
            try {
                sourceFile = copyUriToCache(sourceUri, "evc_mux_source")
                audioFile = copyUriToCache(audioUri, "evc_mux_audio")
                output = File(cacheDir, "evc_tracks_${System.currentTimeMillis()}.mp4")
                val sourceExtractor = MediaExtractor()
                val audioExtractor = MediaExtractor()
                var muxer: MediaMuxer? = null
                var muxerStarted = false
                try {
                    sourceExtractor.setDataSource(sourceFile.absolutePath)
                    audioExtractor.setDataSource(audioFile.absolutePath)
                    // Reject unsupported container codecs before passing their formats to
                    // MediaMuxer. Some Android/vendor muxer implementations terminate the
                    // process in native code for unsupported MP4 track formats.
                    val sourceFormats = (0 until sourceExtractor.trackCount).map { sourceExtractor.getTrackFormat(it) }
                    val allowedVideoMimes = setOf("video/avc", "video/hevc", "video/mp4v-es")
                    val allowedAudioMimes = setOf("audio/mp4a-latm")
                    val unsupportedMp4Formats = sourceFormats.mapNotNull { format ->
                        val mime = format.getString(MediaFormat.KEY_MIME) ?: ""
                        when {
                            mime.startsWith("video/") && mime !in allowedVideoMimes -> mime
                            mime.startsWith("audio/") && mime !in allowedAudioMimes -> mime
                            !mime.startsWith("video/") && !mime.startsWith("audio/") -> mime
                            else -> null
                        }
                    }.distinct()
                    if (unsupportedMp4Formats.isNotEmpty()) throw IllegalStateException(
                        "برای جلوگیری از بسته‌شدن برنامه، این ترک‌های ناسازگار با مسیر امن MP4 وارد خروجی نشدند: ${unsupportedMp4Formats.joinToString()}. از ویدیوی H.264/H.265 با صدای AAC استفاده کنید."
                    )
                    val selectedAudioMimes = (0 until audioExtractor.trackCount).mapNotNull { i ->
                        audioExtractor.getTrackFormat(i).getString(MediaFormat.KEY_MIME)
                            ?.takeIf { it.startsWith("audio/") }
                    }
                    if (selectedAudioMimes.none { it == "audio/mp4a-latm" }) throw IllegalStateException(
                        "فایل صدای انتخابی برای افزودن مستقیم به MP4 باید AAC باشد. ابتدا آن را به AAC تبدیل کنید؛ برنامه برای جلوگیری از قطع‌شدن، این مسیر ناسازگار را اجرا نکرد."
                    )
                    val sourceVideoTracks = (0 until sourceExtractor.trackCount).filter {
                        sourceExtractor.getTrackFormat(it).getString(MediaFormat.KEY_MIME)?.startsWith("video/") == true
                    }
                    if (sourceVideoTracks.isEmpty()) throw IllegalStateException("در فایل اصلی ترک ویدیویی پیدا نشد")
                    val unsupported = (0 until sourceExtractor.trackCount).mapNotNull { i ->
                        val mime = sourceExtractor.getTrackFormat(i).getString(MediaFormat.KEY_MIME) ?: ""
                        if (mime.startsWith("video/") || mime.startsWith("audio/")) null else "$i:$mime"
                    }
                    if (unsupported.isNotEmpty()) throw IllegalStateException(
                        "فایل اصلی ترک‌های غیرصوتی/تصویری دارد (${unsupported.joinToString()})؛ برای جلوگیری از حذف آن‌ها، خروجی لغو شد."
                    )
                    val selectedAudioTrack = (0 until audioExtractor.trackCount).firstOrNull {
                        audioExtractor.getTrackFormat(it).getString(MediaFormat.KEY_MIME)?.startsWith("audio/") == true
                    } ?: throw IllegalStateException("در فایل انتخابی ترک صوتی پیدا نشد")

                    muxer = MediaMuxer(output.absolutePath, MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4)
                    val trackMap = mutableMapOf<Pair<Int, Int>, Int>()
                    for (i in 0 until sourceExtractor.trackCount) {
                        val mime = sourceExtractor.getTrackFormat(i).getString(MediaFormat.KEY_MIME) ?: continue
                        if (mime.startsWith("video/") || mime.startsWith("audio/")) {
                            try {
                                trackMap[0 to i] = muxer.addTrack(sourceExtractor.getTrackFormat(i))
                                sourceExtractor.selectTrack(i)
                            } catch (e: Exception) {
                                throw IllegalStateException("حفظ ترک اصلی $i با کدک $mime توسط MP4 اندروید پشتیبانی نشد؛ خروجی لغو شد.", e)
                            }
                        }
                    }
                    try {
                        trackMap[1 to selectedAudioTrack] = muxer.addTrack(audioExtractor.getTrackFormat(selectedAudioTrack))
                    } catch (e: Exception) {
                        throw IllegalStateException("فرمت صدای انتخابی با ظرف MP4 سازگار نیست؛ یک فایل صوتی AAC را امتحان کنید.", e)
                    }
                    audioExtractor.selectTrack(selectedAudioTrack)
                    muxer.start()
                    muxerStarted = true

                    val durationUs = (videoDurationMs.takeIf { it > 0L } ?: run {
                        val retriever = MediaMetadataRetriever()
                        try {
                            retriever.setDataSource(sourceFile.absolutePath)
                            retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_DURATION)?.toLongOrNull() ?: Long.MAX_VALUE / 1000L
                        } finally { retriever.release() }
                    }) * 1000L
                    val extractors = listOf(sourceExtractor, audioExtractor)
                    val exhausted = BooleanArray(extractors.size)
                    val buffer = java.nio.ByteBuffer.allocate(8 * 1024 * 1024)
                    val info = MediaCodec.BufferInfo()
                    while (true) {
                        var chosenExtractor = -1
                        var chosenTrack = -1
                        var chosenTime = Long.MAX_VALUE
                        for (ei in extractors.indices) {
                            if (exhausted[ei]) continue
                            val ex = extractors[ei]
                            val ti = ex.sampleTrackIndex
                            val time = ex.sampleTime
                            if (ti >= 0 && time >= 0L && time < chosenTime) {
                                chosenExtractor = ei
                                chosenTrack = ti
                                chosenTime = time
                            }
                        }
                        if (chosenExtractor < 0) break
                        val ex = extractors[chosenExtractor]
                        if (chosenTime <= durationUs) {
                            buffer.clear()
                            val size = ex.readSampleData(buffer, 0)
                            if (size > buffer.capacity()) throw IllegalStateException("نمونهٔ صوتی/تصویری از ظرفیت بافر بیشتر است")
                            if (size > 0) {
                                val outputTrack = trackMap[chosenExtractor to chosenTrack]
                                    ?: throw IllegalStateException("نگاشت ترک خروجی پیدا نشد")
                                info.set(0, size, chosenTime, ex.sampleFlags)
                                muxer.writeSampleData(outputTrack, buffer, info)
                            }
                        }
                        if (!ex.advance()) exhausted[chosenExtractor] = true
                    }
                } finally {
                    if (muxerStarted) try { muxer?.stop() } catch (_: Exception) { }
                    try { muxer?.release() } catch (_: Exception) { }
                    sourceExtractor.release()
                    audioExtractor.release()
                }
                if (!output.exists() || output.length() == 0L) throw IllegalStateException("فایل خروجی ساخته نشد")
            } catch (e: Exception) {
                error = e.message ?: e.javaClass.simpleName
                output?.delete()
                output = null
            } finally {
                sourceFile?.delete()
                audioFile?.delete()
            }
            mainHandler.post {
                button.isEnabled = true
                findViewById<Button>(R.id.addAudioButton).isEnabled = true
                findViewById<Button>(R.id.addSubtitleButton).isEnabled = true
                val result = output
                if (result == null || !result.exists() || result.length() == 0L) {
                    statusText.text = "افزودن ترک صوتی ناموفق بود: ${error ?: "خطای ناشناخته"}"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                    result?.delete()
                    return@post
                }
                try {
                    val values = ContentValues().apply {
                        put(MediaStore.Video.Media.DISPLAY_NAME, requestedOutputDisplayName("EVC_tracks_${System.currentTimeMillis()}", "mp4"))
                        put(MediaStore.Video.Media.MIME_TYPE, "video/mp4")
                        if (android.os.Build.VERSION.SDK_INT >= 29) {
                            put(MediaStore.Video.Media.RELATIVE_PATH, Environment.DIRECTORY_MOVIES + "/EVC")
                            put(MediaStore.Video.Media.IS_PENDING, 1)
                        }
                    }
                    val outUri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
                        ?: throw IllegalStateException("ساخت فایل در Movies/EVC ممکن نشد")
                    contentResolver.openOutputStream(outUri)?.use { stream -> FileInputStream(result).use { it.copyTo(stream) } }
                        ?: throw IllegalStateException("نوشتن فایل خروجی ناموفق بود")
                    if (android.os.Build.VERSION.SDK_INT >= 29) {
                        contentResolver.update(outUri, ContentValues().apply { put(MediaStore.Video.Media.IS_PENDING, 0) }, null, null)
                    }
                    result.delete()
                    restoreNormalStoryboardAfterExport()
                    statusText.text = "ترک صوتی جدید به‌صورت جداگانه افزوده شد؛ صدای اصلی و ویدیو حفظ شدند و ویدیو دوباره رمزگذاری نشد."
                    Toast.makeText(this, "خروجی در Movies/EVC ذخیره شد", Toast.LENGTH_LONG).show()
                } catch (e: Exception) {
                    result.delete()
                    statusText.text = "ذخیرهٔ خروجی ناموفق بود: ${e.message ?: "خطا"}"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                }
            }
        }
    }

    /** Replaces the source soundtrack with the selected audio through Media3 Transformer. */
    @androidx.media3.common.util.UnstableApi
    private fun exportAudioReplacementWithTransformer(
        sourceUri: Uri, audioUri: Uri, text: String, textSize: Int, textX: Int, textY: Int
    ) {
        val button = findViewById<Button>(R.id.outputChangesButton)
        button.isEnabled = false
        statusText.text = "در حال ساخت خروجی صدا با موتور داخلی اندروید…"
        val output = File(cacheDir, "evc_audio_${System.currentTimeMillis()}.mp4")
        try {
            val videoEffects = mutableListOf<androidx.media3.common.Effect>()
            if (text.isNotEmpty()) {
                val styledText = SpannableString(text).apply {
                    setSpan(ForegroundColorSpan(Color.WHITE), 0, length, Spannable.SPAN_EXCLUSIVE_EXCLUSIVE)
                    setSpan(StyleSpan(Typeface.BOLD), 0, length, Spannable.SPAN_EXCLUSIVE_EXCLUSIVE)
                }
                val anchorX = (-1f + 2f * textX.coerceIn(0, 100) / 100f).coerceIn(-1f, 1f)
                val anchorY = (1f - 2f * textY.coerceIn(0, 100) / 100f).coerceIn(-1f, 1f)
                val scale = (textSize / 100f).coerceIn(0.08f, 1.6f)
                val settings = StaticOverlaySettings.Builder()
                    .setOverlayFrameAnchor(-1f, 1f)
                    .setBackgroundFrameAnchor(anchorX, anchorY)
                    .setScale(scale, scale)
                    .build()
                videoEffects.add(OverlayEffect(listOf(TextOverlay.createStaticTextOverlay(styledText, settings))))
            }
            val videoItemBuilder = EditedMediaItem.Builder(MediaItem.fromUri(sourceUri)).setRemoveAudio(true)
            if (videoEffects.isNotEmpty()) videoItemBuilder.setEffects(Effects(emptyList(), videoEffects))
            val videoSequence = EditedMediaItemSequence.Builder(videoItemBuilder.build()).build()
            val targetDurationMs = videoDurationMs.takeIf { it > 0L } ?: run {
                val retriever = MediaMetadataRetriever()
                try {
                    retriever.setDataSource(this, sourceUri)
                    retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_DURATION)?.toLongOrNull() ?: 0L
                } finally { retriever.release() }
            }
            val audioMediaItem = if (targetDurationMs > 0L) {
                MediaItem.Builder().setUri(audioUri).setClippingConfiguration(
                    MediaItem.ClippingConfiguration.Builder().setEndPositionMs(targetDurationMs).build()
                ).build()
            } else MediaItem.fromUri(audioUri)
            val audioItem = EditedMediaItem.Builder(audioMediaItem).setRemoveVideo(true).build()
            val audioSequence = EditedMediaItemSequence.Builder(audioItem).build()
            val composition = Composition.Builder(listOf(videoSequence, audioSequence)).build()
            val transformer = Transformer.Builder(this).addListener(object : Transformer.Listener {
                override fun onCompleted(composition: Composition, exportResult: ExportResult) {
                    activeTransformer = null
                    try {
                        val values = ContentValues().apply {
                            put(MediaStore.Video.Media.DISPLAY_NAME, requestedOutputDisplayName("EVC_audio_${System.currentTimeMillis()}", "mp4"))
                            put(MediaStore.Video.Media.MIME_TYPE, "video/mp4")
                            if (android.os.Build.VERSION.SDK_INT >= 29) {
                                put(MediaStore.Video.Media.RELATIVE_PATH, Environment.DIRECTORY_MOVIES + "/EVC")
                                put(MediaStore.Video.Media.IS_PENDING, 1)
                            }
                        }
                        val outUri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
                            ?: throw IllegalStateException("ساخت فایل در Movies/EVC ممکن نشد")
                        contentResolver.openOutputStream(outUri)?.use { stream -> FileInputStream(output).use { it.copyTo(stream) } }
                            ?: throw IllegalStateException("نوشتن فایل خروجی ناموفق بود")
                        if (android.os.Build.VERSION.SDK_INT >= 29) {
                            contentResolver.update(outUri, ContentValues().apply { put(MediaStore.Video.Media.IS_PENDING, 0) }, null, null)
                        }
                        output.delete()
                        button.isEnabled = true
                    restoreNormalStoryboardAfterExport()
                        statusText.text = if (text.isNotEmpty()) "متن و صدای انتخابی در Movies/EVC ذخیره شدند؛ صدای اصلی جایگزین شد." else "صدای انتخابی در Movies/EVC جایگزین صدای اصلی شد."
                        Toast.makeText(this@MainActivity, statusText.text, Toast.LENGTH_LONG).show()
                    } catch (e: Exception) {
                        output.delete(); button.isEnabled = true
                        statusText.text = "ذخیرهٔ خروجی صدا ناموفق بود: ${e.message ?: "خطا"}"
                        Toast.makeText(this@MainActivity, statusText.text, Toast.LENGTH_LONG).show()
                    }
                }
                override fun onError(composition: Composition, exportResult: ExportResult, exportException: ExportException) {
                    activeTransformer = null
                    output.delete(); button.isEnabled = true
                    statusText.text = "ساخت خروجی صدا ناموفق بود: ${exportException.message ?: "خطای رمزگذاری"}"
                    Toast.makeText(this@MainActivity, statusText.text, Toast.LENGTH_LONG).show()
                }
            }).build()
            activeTransformer = transformer
            transformer.start(composition, output.absolutePath)
        } catch (e: Exception) {
            activeTransformer = null
            output.delete(); button.isEnabled = true
            statusText.text = "شروع خروجی صدا ناموفق بود: ${e.message ?: e.javaClass.simpleName}"
            Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
        }
    }

    /** Text-only export through Media3 Transformer, avoiding FFmpegKit native execution. */
    @androidx.media3.common.util.UnstableApi
    private fun exportTextOnlyWithTransformer(sourceUri: Uri, text: String, textSize: Int, textX: Int, textY: Int) {
        val button = findViewById<Button>(R.id.outputChangesButton)
        button.isEnabled = false
        statusText.text = "در حال ساخت خروجی متن با موتور داخلی اندروید…"
        val output = File(cacheDir, "evc_text_${System.currentTimeMillis()}.mp4")
        try {
            val styledText = SpannableString(text).apply {
                if (isNotEmpty()) {
                    setSpan(ForegroundColorSpan(Color.WHITE), 0, length, Spannable.SPAN_EXCLUSIVE_EXCLUSIVE)
                    setSpan(StyleSpan(Typeface.BOLD), 0, length, Spannable.SPAN_EXCLUSIVE_EXCLUSIVE)
                }
            }
            val anchorX = (-1f + 2f * textX.coerceIn(0, 100) / 100f).coerceIn(-1f, 1f)
            val anchorY = (1f - 2f * textY.coerceIn(0, 100) / 100f).coerceIn(-1f, 1f)
            val scale = (textSize / 100f).coerceIn(0.08f, 1.6f)
            val overlaySettings = StaticOverlaySettings.Builder()
                .setOverlayFrameAnchor(-1f, 1f)
                .setBackgroundFrameAnchor(anchorX, anchorY)
                .setScale(scale, scale)
                .build()
            val textOverlay = TextOverlay.createStaticTextOverlay(styledText, overlaySettings)
            val overlayEffect = OverlayEffect(listOf(textOverlay))
            val item = EditedMediaItem.Builder(MediaItem.fromUri(sourceUri))
                .setEffects(Effects(emptyList(), listOf(overlayEffect)))
                .build()
            val composition = Composition.Builder(EditedMediaItemSequence.Builder(item).build()).build()
            val transformer = Transformer.Builder(this).addListener(object : Transformer.Listener {
                override fun onCompleted(composition: Composition, exportResult: ExportResult) {
                    activeTransformer = null
                    try {
                        val values = ContentValues().apply {
                            put(MediaStore.Video.Media.DISPLAY_NAME, requestedOutputDisplayName("EVC_Text_${System.currentTimeMillis()}", "mp4"))
                            put(MediaStore.Video.Media.MIME_TYPE, "video/mp4")
                            if (android.os.Build.VERSION.SDK_INT >= 29) {
                                put(MediaStore.Video.Media.RELATIVE_PATH, Environment.DIRECTORY_MOVIES + "/EVC")
                                put(MediaStore.Video.Media.IS_PENDING, 1)
                            }
                        }
                        val outUri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
                            ?: throw IllegalStateException("ساخت فایل در Movies/EVC ممکن نشد")
                        contentResolver.openOutputStream(outUri)?.use { stream -> FileInputStream(output).use { it.copyTo(stream) } }
                            ?: throw IllegalStateException("نوشتن فایل خروجی ناموفق بود")
                        if (android.os.Build.VERSION.SDK_INT >= 29) {
                            contentResolver.update(outUri, ContentValues().apply {
                                put(MediaStore.Video.Media.IS_PENDING, 0)
                            }, null, null)
                        }
                        output.delete()
                        button.isEnabled = true
                    restoreNormalStoryboardAfterExport()
                        statusText.text = "متن روی ویدیو در Movies/EVC ذخیره شد."
                        Toast.makeText(this@MainActivity, statusText.text, Toast.LENGTH_LONG).show()
                    } catch (e: Exception) {
                        output.delete(); button.isEnabled = true
                        statusText.text = "ذخیرهٔ خروجی متن ناموفق بود: ${e.message ?: "خطا"}"
                        Toast.makeText(this@MainActivity, statusText.text, Toast.LENGTH_LONG).show()
                    }
                }
                override fun onError(composition: Composition, exportResult: ExportResult, exportException: ExportException) {
                    activeTransformer = null
                    output.delete(); button.isEnabled = true
                    statusText.text = "ساخت خروجی متن ناموفق بود: ${exportException.message ?: "خطای رمزگذاری"}"
                    Toast.makeText(this@MainActivity, statusText.text, Toast.LENGTH_LONG).show()
                }
            }).build()
            activeTransformer = transformer
            transformer.start(composition, output.absolutePath)
        } catch (e: Exception) {
            activeTransformer = null
            output.delete(); button.isEnabled = true
            statusText.text = "شروع خروجی متن ناموفق بود: ${e.message ?: e.javaClass.simpleName}"
            Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
        }
    }

    private fun showOverlayVideoPreview(uri: Uri) {
        releaseOverlayPreviewPlayer()
        overlayVideoLayer.visibility = View.VISIBLE
        overlayPreviewTexture.visibility = View.VISIBLE
        try {
            contentResolver.openAssetFileDescriptor(uri, "r")?.use { afd ->
                val retriever = MediaMetadataRetriever()
                try {
                    retriever.setDataSource(this, uri)
                    overlayPreviewVideoWidth = retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_VIDEO_WIDTH)?.toIntOrNull()?.coerceAtLeast(1) ?: 16
                    overlayPreviewVideoHeight = retriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_VIDEO_HEIGHT)?.toIntOrNull()?.coerceAtLeast(1) ?: 9
                } finally { retriever.release() }
            }
            updateOverlayPreviewLayout()
            if (overlayPreviewTexture.isAvailable) overlayPreviewTexture.surfaceTexture?.let { startOverlayPreviewOnSurface(it) }
        } catch (e: Exception) {
            overlayVideoLayer.visibility = View.GONE
            statusText.text = "پیش‌نمایش ویدیوی رویی باز نشد: ${e.message ?: "قالب یا دسترسی فایل پشتیبانی نمی‌شود"}"
            Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
        }
    }

    private fun startOverlayPreviewOnSurface(surfaceTexture: SurfaceTexture) {
        val uri = overlayVideoUri ?: return
        releaseOverlayPreviewPlayer()
        try {
            val player = MediaPlayer()
            overlayPreviewSurface = Surface(surfaceTexture)
            player.setSurface(overlayPreviewSurface)
            player.setDataSource(this, uri)
            player.isLooping = true
            player.setVolume(0f, 0f) // Preview is muted; the final output controls the actual soundtrack.
            player.setOnPreparedListener { mp ->
                overlayPreviewVideoWidth = mp.videoWidth.coerceAtLeast(1)
                overlayPreviewVideoHeight = mp.videoHeight.coerceAtLeast(1)
                updateOverlayPreviewLayout()
                try { mp.start() } catch (_: Exception) { }
            }
            player.setOnErrorListener { _, what, extra ->
                runOnUiThread {
                    statusText.text = "انتخاب شد، اما این ویدیو در پیش‌نمایش پخش نشد ($what/$extra)؛ خروجی را می‌توان جداگانه امتحان کرد"
                }
                true
            }
            overlayPreviewPlayer = player
            player.prepareAsync()
        } catch (e: Exception) {
            releaseOverlayPreviewPlayer()
            statusText.text = "پخش پیش‌نمایش ویدیوی رویی ناموفق بود: ${e.message ?: "قالب ویدیو پشتیبانی نمی‌شود"}"
        }
    }

    private fun updateOverlayVideoVisibility(positionMs: Long) {
        if (!::overlayVideoLayer.isInitialized || overlayVideoUri == null) return
        val start = parseTimeInput(findViewById<EditText>(R.id.overlayVideoStartTime).text.toString()) ?: 0L
        val end = parseTimeInput(findViewById<EditText>(R.id.overlayVideoEndTime).text.toString()) ?: videoDurationMs
        val active = positionMs in start..end
        overlayVideoLayer.visibility = if (active) View.VISIBLE else View.GONE
        try {
            val player = overlayPreviewPlayer
            if (active && videoView.isPlaying) {
                if (player != null && !player.isPlaying) player.start()
            } else if (player != null && player.isPlaying) player.pause()
        } catch (_: Exception) { }
    }

    private fun updateOverlayPreviewLayout() {
        if (!::overlayVideoLayer.isInitialized || !::overlayPreviewTexture.isInitialized) return
        val layerWidth = overlayVideoLayer.width
        val layerHeight = overlayVideoLayer.height
        if (layerWidth <= 0 || layerHeight <= 0) {
            overlayVideoLayer.post { updateOverlayPreviewLayout() }
            return
        }
        val widthPct = overlayVideoWidthPercent.coerceIn(5, 90)
        val x = overlayVideoXPercent.coerceIn(0, 100 - widthPct)
        val y = overlayVideoYPercent.coerceIn(0, 95)
        val w = (layerWidth * widthPct / 100f).toInt().coerceAtLeast(1)
        val aspect = overlayPreviewVideoWidth.toFloat() / overlayPreviewVideoHeight.coerceAtLeast(1)
        val h = (w / aspect).toInt().coerceIn(1, layerHeight)
        val left = (layerWidth * x / 100f).toInt().coerceAtMost((layerWidth - w).coerceAtLeast(0))
        val top = (layerHeight * y / 100f).toInt().coerceAtMost((layerHeight - h).coerceAtLeast(0))
        val lp = overlayPreviewTexture.layoutParams as FrameLayout.LayoutParams
        lp.width = w
        lp.height = h
        lp.gravity = Gravity.TOP or Gravity.START
        lp.leftMargin = left
        lp.topMargin = top
        overlayPreviewTexture.layoutParams = lp
        // Keep the draggable selection frame aligned with the actual preview rectangle.
        val aspectForFrame = overlayPreviewVideoWidth.toFloat() / overlayPreviewVideoHeight.coerceAtLeast(1)
        val frameHeightPct = (widthPct * layerWidth.toFloat() / layerHeight.toFloat() / aspectForFrame * 100f).toInt().coerceIn(5, 95)
        if (::placementOverlay.isInitialized && placementMode == PlacementOverlayView.Mode.VIDEO) {
            placementOverlay.setSelection(x, y, widthPct, frameHeightPct)
        }
    }

    private fun releaseOverlayPreviewPlayer() {
        try { overlayPreviewPlayer?.setOnPreparedListener(null); overlayPreviewPlayer?.setOnErrorListener(null); overlayPreviewPlayer?.stop() } catch (_: Exception) { }
        try { overlayPreviewPlayer?.release() } catch (_: Exception) { }
        overlayPreviewPlayer = null
        try { overlayPreviewSurface?.release() } catch (_: Exception) { }
        overlayPreviewSurface = null
    }

    private fun chooseOverlayVideo() {
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE)
            type = "video/*"
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        }
        try { startActivityForResult(intent, PICK_OVERLAY_VIDEO) }
        catch (_: Exception) { Toast.makeText(this, "انتخاب‌گر ویدیو در دسترس نیست", Toast.LENGTH_LONG).show() }
    }

    /** Burns text and/or composites a second video over the selected source. */
    private fun exportTextAndVideoOverlay() {
        val sourceUri = selectedUri
        if (sourceUri == null) {
            Toast.makeText(this, "ابتدا ویدیوی اصلی را انتخاب کنید", Toast.LENGTH_LONG).show()
            return
        }
        val text = findViewById<EditText>(R.id.overlayTextInput).text.toString().trim()
        val secondUri = overlayVideoUri
        val audioUri = externalAudioUri
        if (text.isEmpty() && secondUri == null && audioUri == null) {
            Toast.makeText(this, "متن وارد کنید، ویدیوی رویی یا فایل صوتی انتخاب کنید", Toast.LENGTH_LONG).show()
            return
        }
        fun number(id: Int, fallback: Int, min: Int = 0, max: Int = 100): Int =
            findViewById<EditText>(id).text.toString().toIntOrNull()?.coerceIn(min, max) ?: fallback
        val textSize = liveTextSize.coerceIn(8, 160)
        val textX = textXPercent.coerceIn(0, 100)
        val textY = textYPercent.coerceIn(0, 100)
        val textStartMs = parseTimeInput(findViewById<EditText>(R.id.overlayTextStartTime).text.toString())
        val textEndMs = parseTimeInput(findViewById<EditText>(R.id.overlayTextEndTime).text.toString())
        if (text.isNotEmpty()) {
            if (textStartMs == null || textEndMs == null || textEndMs <= textStartMs) {
                Toast.makeText(this, "زمان شروع و پایان متن را درست وارد کنید؛ پایان باید بعد از شروع باشد", Toast.LENGTH_LONG).show()
                return
            }
            if (videoDurationMs > 0L && textEndMs > videoDurationMs) {
                Toast.makeText(this, "زمان پایان متن از مدت ویدیو بیشتر است", Toast.LENGTH_LONG).show()
                return
            }
        }
        val fullDurationText = text.isNotEmpty() && textStartMs == 0L &&
            (videoDurationMs <= 0L || (textEndMs ?: 0L) >= videoDurationMs)
        val videoWidth = overlayVideoWidthPercent.coerceIn(5, 90)
        val videoX = overlayVideoXPercent.coerceIn(0, 100 - videoWidth)
        val videoY = overlayVideoYPercent.coerceIn(0, 95)
        if (videoX + videoWidth > 100 || videoY >= 100) {
            Toast.makeText(this, "جایگاه یا عرض ویدیوی رویی نامعتبر است", Toast.LENGTH_LONG).show()
            return
        }
        // Keep common MP4 exports on Media3 rather than the FFmpegKit JNI path.
        // Text-only already uses this route; audio replacement now uses a parallel audio
        // sequence, while the source video sequence has its original audio removed.
        // Use Media3 Transformer only for audio-only replacement. Text rendering is routed
        // through the guarded FFmpeg worker below for both full-duration and timed text:
        // this avoids the device-level native crash observed on some ARM32 phones while
        // applying Media3 OverlayEffect during export.
        if (secondUri == null && !outputContainerMatroska && text.isEmpty() && audioUri != null) {
            exportAudioReplacementWithTransformer(sourceUri, audioUri, text, textSize, textX, textY)
            return
        }
        val button = findViewById<Button>(R.id.outputChangesButton)
        button.isEnabled = false
        statusText.text = "در حال ساخت خروجی متن/ویدیو/صدا…"
        worker.execute {
            var baseFile: File? = null
            var overlayFile: File? = null
            var audioFile: File? = null
            var textFile: File? = null
            var output: File? = null
            var error: String? = null
            try {
                baseFile = copyUriToCache(sourceUri, "evc_overlay_base")
                if (secondUri != null) overlayFile = copyUriToCache(secondUri, "evc_overlay_video")
                if (audioUri != null) audioFile = copyUriToCache(audioUri, "evc_overlay_audio")
                if (text.isNotEmpty()) {
                    textFile = File(cacheDir, "evc_overlay_text_${System.currentTimeMillis()}.txt")
                    textFile.writeText(text, Charsets.UTF_8)
                }
                val ext = outputExtension()
                output = File(cacheDir, "evc_overlay_${System.currentTimeMillis()}.$ext")
                val graph = mutableListOf<String>()
                var current = "0:v"
                if (overlayFile != null) {
                    graph.add("[1:v][0:v]scale2ref=w=main_w*$videoWidth/100:h=ow/mdar[evc_small][evc_base]")
                    graph.add("[evc_base][evc_small]overlay=x='main_w*$videoX/100':y='main_h*$videoY/100':eof_action=pass[evc_with_video]")
                    current = "evc_with_video"
                }
                if (textFile != null) {
                    val safePath = textFile.absolutePath.replace("\\", "\\\\").replace(":", "\\:").replace("'", "\\'")
                    val startSeconds = ((textStartMs ?: 0L).toDouble() / 1000.0).let { String.format(java.util.Locale.US, "%.3f", it) }
                    val endSeconds = ((textEndMs ?: videoDurationMs).toDouble() / 1000.0).let { String.format(java.util.Locale.US, "%.3f", it) }
                    val timingFilter = if (text.isNotEmpty()) ":enable='between(t\\,$startSeconds\\,$endSeconds)'" else ""
                    val draw = "drawtext=fontfile='/system/fonts/Roboto-Regular.ttf':textfile='$safePath':fontsize=$textSize:fontcolor=white:borderw=2:bordercolor=black:x='w*$textX/100':y='h*$textY/100'$timingFilter"
                    graph.add("[$current]$draw[evc_text_out]")
                    current = "evc_text_out"
                }
                // Keep text/overlay encoding conservative on 32-bit ARM devices: one filter thread,
                // one encoder thread, no look-ahead/MB-tree, and a single reference frame.
                val args = mutableListOf(
                    "-y",
                    "-filter_threads", "1",
                    "-filter_complex_threads", "1",
                    "-threads", "1",
                    "-i", baseFile.absolutePath
                )
                var nextInputIndex = 1
                if (overlayFile != null) {
                    args.addAll(listOf("-stream_loop", "-1", "-i", overlayFile.absolutePath))
                    nextInputIndex++
                }
                val audioInputIndex = if (audioFile != null) nextInputIndex else null
                if (audioFile != null) args.addAll(listOf("-i", audioFile.absolutePath))
                if (graph.isNotEmpty()) {
                    args.addAll(listOf("-filter_complex", graph.joinToString(";"), "-map", "[$current]"))
                } else {
                    args.addAll(listOf("-map", "0:v:0"))
                }
                if (audioInputIndex != null) {
                    // The selected external audio replaces the source soundtrack; pad it to video duration.
                    args.addAll(listOf("-map", "$audioInputIndex:a:0", "-af", "apad", "-c:a", "aac", "-b:a", "192k", "-shortest"))
                } else {
                    args.addAll(listOf("-map", "0:a?", "-c:a", "copy"))
                }
                args.addAll(listOf(
                    "-c:v", "libx264",
                    "-preset", "ultrafast",
                    "-tune", "fastdecode",
                    "-threads", "1",
                    "-x264-params", "threads=1:sliced-threads=1:lookahead_threads=1:sync-lookahead=0:rc-lookahead=0:mbtree=0:ref=1:bframes=0:me=dia:subme=0:partitions=none:8x8dct=0:weightp=0:aq-mode=0",
                    "-crf", "20",
                    "-pix_fmt", "yuv420p"
                ))
                if (!outputContainerMatroska) args.addAll(listOf("-movflags", "+faststart"))
                args.addAll(listOf("-max_muxing_queue_size", "512", "-f", if (outputContainerMatroska) "matroska" else "mp4", output.absolutePath))
                val session = FFmpegKit.executeWithArguments(args.toTypedArray())
                if (!ReturnCode.isSuccess(session.returnCode) || !output.exists() || output.length() == 0L) {
                    throw IllegalStateException("ساخت خروجی متن/ویدیو ناموفق بود: ${session.allLogsAsString.takeLast(1400)}")
                }
            } catch (e: Exception) {
                error = e.message ?: e.javaClass.simpleName
                output?.delete(); output = null
            } finally {
                baseFile?.delete(); overlayFile?.delete(); audioFile?.delete(); textFile?.delete()
            }
            mainHandler.post {
                button.isEnabled = true
                val result = output
                if (result == null || !result.exists() || result.length() == 0L) {
                    statusText.text = "ساخت خروجی متن/ویدیو ناموفق بود: ${error ?: "خطای ناشناخته"}"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                    result?.delete()
                    return@post
                }
                try {
                    val ext = outputExtension()
                    val values = ContentValues().apply {
                        put(MediaStore.Video.Media.DISPLAY_NAME, requestedOutputDisplayName("EVC_overlay_${System.currentTimeMillis()}", ext))
                        put(MediaStore.Video.Media.MIME_TYPE, outputMimeType())
                        if (android.os.Build.VERSION.SDK_INT >= 29) {
                            put(MediaStore.Video.Media.RELATIVE_PATH, Environment.DIRECTORY_MOVIES + "/EVC")
                            put(MediaStore.Video.Media.IS_PENDING, 1)
                        }
                    }
                    val outUri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
                        ?: throw IllegalStateException("ساخت فایل در Movies/EVC ممکن نشد")
                    contentResolver.openOutputStream(outUri)?.use { stream -> FileInputStream(result).use { it.copyTo(stream) } }
                        ?: throw IllegalStateException("نوشتن فایل خروجی ناموفق بود")
                    if (android.os.Build.VERSION.SDK_INT >= 29) {
                        contentResolver.update(outUri, ContentValues().apply { put(MediaStore.Video.Media.IS_PENDING, 0) }, null, null)
                    }
                    result.delete()
                    restoreNormalStoryboardAfterExport()
                    statusText.text = when {
                        audioUri != null && text.isNotEmpty() && secondUri != null -> "متن، ویدیوی رویی و صدای انتخابی در Movies/EVC ذخیره شدند؛ صدای انتخابی جای صدای اصلی را گرفت."
                        audioUri != null && text.isNotEmpty() -> "متن و صدای انتخابی در Movies/EVC ذخیره شدند؛ صدای انتخابی جای صدای اصلی را گرفت."
                        audioUri != null && secondUri != null -> "ویدیوی رویی و صدای انتخابی در Movies/EVC ذخیره شدند؛ صدای انتخابی جای صدای اصلی را گرفت."
                        audioUri != null -> "ویدیو با صدای انتخابی در Movies/EVC ذخیره شد؛ صدای انتخابی جای صدای اصلی را گرفت."
                        text.isNotEmpty() && secondUri != null -> "متن و ویدیوی رویی ترکیب و در Movies/EVC ذخیره شدند؛ ویدیو دوباره رمزگذاری شده است."
                        text.isNotEmpty() -> "متن روی ویدیو در Movies/EVC ذخیره شد."
                        else -> "ویدیوی رویی در Movies/EVC ذخیره شد."
                    }
                    Toast.makeText(this, "خروجی در Movies/EVC ذخیره شد", Toast.LENGTH_LONG).show()
                } catch (e: Exception) {
                    result.delete()
                    statusText.text = "ذخیرهٔ خروجی ناموفق بود: ${e.message ?: "خطا"}"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                }
            }
        }
    }

    /** Keeps effect selection and the blur controls visibly synchronized. Effects apply only to exported output. */

    /** Applies selected FFmpeg video filters to the full video, with optional rectangular blur. */

    private fun updateLiveTextPreview() {
        val text = findViewById<EditText>(R.id.overlayTextInput).text.toString()
        val panelOpen = findViewById<View>(R.id.textOverlayPanel).visibility == View.VISIBLE
        if (text.isNotBlank() && selectedUri != null && panelOpen) {
            placementMode = PlacementOverlayView.Mode.TEXT
            placementOverlay.setMode(PlacementOverlayView.Mode.TEXT)
            placementOverlay.setSelection(textXPercent, textYPercent, 40, 20)
            placementOverlay.setTextPreview(text, liveTextSize)
            placementOverlay.visibility = View.VISIBLE
            placementOverlay.bringToFront()
        } else if (placementMode == PlacementOverlayView.Mode.TEXT) {
            placementOverlay.visibility = View.GONE
        }
    }

    private fun activatePlacementMode(mode: PlacementOverlayView.Mode) {
        if (mode == PlacementOverlayView.Mode.TEXT) recordUndoState()
        placementMode = mode
        val readPercent: (Int, Int) -> Int = { id, fallback -> findViewById<EditText>(id).text.toString().toIntOrNull()?.coerceIn(0, 100) ?: fallback }
        val x: Int
        val y: Int
        val w: Int
        val h: Int
        when (mode) {
            PlacementOverlayView.Mode.TEXT -> { x = textXPercent; y = textYPercent; w = 40; h = 20 }
            PlacementOverlayView.Mode.VIDEO -> { x = overlayVideoXPercent; y = overlayVideoYPercent; w = overlayVideoWidthPercent.coerceIn(5, 90); h = (w * 9 / 16).coerceAtLeast(8) }
            else -> { placementOverlay.visibility = View.GONE; return }
        }
        placementOverlay.setMode(mode)
        placementOverlay.setSelection(x, y, w, h)
        if (mode == PlacementOverlayView.Mode.TEXT) {
            val enteredText = findViewById<EditText>(R.id.overlayTextInput).text.toString()
            placementOverlay.setTextPreview(enteredText, liveTextSize)
        }
        placementOverlay.visibility = View.VISIBLE
        placementOverlay.bringToFront()
        if (mode == PlacementOverlayView.Mode.VIDEO) {
            overlayVideoLayer.visibility = View.VISIBLE
            updateOverlayPreviewLayout()
        }
        statusText.text = when (mode) {
            PlacementOverlayView.Mode.TEXT -> "جای متن را روی پلیر لمس کن و بکش؛ محل متن خودکار ثبت می‌شود"
            PlacementOverlayView.Mode.VIDEO -> "پیش‌نمایش واقعی ویدیوی رویی روی پلیر نمایش داده می‌شود؛ برای جابه‌جایی کادر را بکش و برای تغییر اندازه گوشه‌ها را بکش"
            else -> ""
        }
    }

    private fun chooseVideo() {
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE)
            type = "video/*"
            putExtra(Intent.EXTRA_ALLOW_MULTIPLE, true)
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        }
        try { startActivityForResult(intent, REQUEST_VIDEO) }
        catch (_: Exception) { Toast.makeText(this, "انتخاب‌گر فایل در دسترس نیست", Toast.LENGTH_LONG).show() }
    }

    /** Automatically rebuilds the storyboard two seconds after the user finishes editing a time field. */
    private fun installStoryboardAutoApply() {
        val watcher = object : TextWatcher {
            override fun beforeTextChanged(s: CharSequence?, start: Int, count: Int, after: Int) = Unit
            override fun onTextChanged(s: CharSequence?, start: Int, before: Int, count: Int) = Unit
            override fun afterTextChanged(s: Editable?) {
                if (suppressStoryboardAutoApply) return
                mainHandler.removeCallbacks(storyboardAutoApplyRunnable)
                mainHandler.postDelayed(storyboardAutoApplyRunnable, 2_000L)
            }
        }
        listOf(R.id.storyboardStartTime, R.id.storyboardEndTime, R.id.storyboardIntervalTime).forEach { id ->
            findViewById<EditText>(id).addTextChangedListener(watcher)
        }
    }

    private fun storyboardColumns(): Int {
        val railWidth = findViewById<View>(R.id.standaloneActionsRail).width.takeIf { it > 0 } ?: dp(85)
        val available = storyboardRows.width.takeIf { it > 0 } ?: (resources.displayMetrics.widthPixels - railWidth - dp(12)).coerceAtLeast(dp(150))
        userStoryboardColumns?.let { return it.coerceIn(2, 15) }
        val target = dp(if (allViewMode) 150 else 126)
        return (available / target).coerceIn(1, if (allViewMode) 8 else 7)
    }

    private fun storyboardCellHeight(): Int {
        val width = (((storyboardRows.width.takeIf { it > 0 } ?: (resources.displayMetrics.widthPixels - dp(95)).coerceAtLeast(dp(150))) / storyboardColumns()) - dp(4)).coerceAtLeast(dp(32))
        val videoAspect = if (sourceVideoWidth > 0 && sourceVideoHeight > 0) sourceVideoWidth.toFloat() / sourceVideoHeight.toFloat() else 16f / 9f
        // The outer cell follows the source frame exactly; labels/badges overlay the image.
        return (width / videoAspect.coerceIn(0.25f, 4f)).toInt().coerceAtLeast(dp(32))
    }

    private fun setAllViewMode(enabled: Boolean) {
        if (allViewMode == enabled) return
        allViewMode = enabled
        val scroll = findViewById<ScrollView>(R.id.mainScrollView)
        val content = scroll.getChildAt(0) as? ViewGroup ?: return
        val section = findViewById<View>(R.id.storyboardSection)
        val playerRow = findViewById<View>(R.id.playerActionRow)

        // All View contains only the storyboard command row and its table.
        // The player and every other editor panel/control are hidden in this mode.
        for (i in 0 until content.childCount) {
            val child = content.getChildAt(i)
            child.visibility = if (!enabled || child === section) View.VISIBLE else View.GONE
        }
        playerRow.visibility = if (enabled) View.GONE else View.VISIBLE
        // Hide the app-wide tools rail too: All View must contain only storyboard controls.
        findViewById<View>(R.id.standaloneActionsRail).visibility = if (enabled) View.GONE else View.VISIBLE
        findViewById<View>(R.id.editorTitle).visibility = if (enabled) View.GONE else View.VISIBLE
        findViewById<View>(R.id.statusText).visibility = if (enabled) View.GONE else View.VISIBLE

        val colorControls = findViewById<View>(R.id.fixedColorControls)
        if (enabled) {
            allViewPreviousColorVisibility = colorControls.visibility
            colorControls.visibility = View.GONE
        } else {
            colorControls.visibility = allViewPreviousColorVisibility
        }

        // The All View layout is intentionally storyboard-only. The player row is
        // hidden entirely; returning restores its normal full-height preview.
        playerRow.layoutParams = playerRow.layoutParams.apply { height = dp(220) }
        val playerContainer = findViewById<View>(R.id.playerContainer)
        playerContainer.layoutParams = (playerContainer.layoutParams as LinearLayout.LayoutParams).apply {
            width = 0
            height = ViewGroup.LayoutParams.MATCH_PARENT
            weight = 1f
        }

        // Keep only the storyboard's command row; hide status/range/cover extras in All View.
        findViewById<View>(R.id.selectionText).visibility = if (enabled) View.GONE else View.VISIBLE
        intArrayOf(
            R.id.timelinePanel,
            R.id.trackPanel,
            R.id.textOverlayPanel,
            R.id.overlayVideoPanel,
            R.id.timelineActionButtons,
            R.id.storyboardTimeRangeRow,
            R.id.freeCropControls
        ).forEach { findViewById<View>(it)?.visibility = View.GONE }
        freeCropMode = false
        cropOverlay.visibility = View.GONE
        if (::timeModeButton.isInitialized) timeModeButton.text = "نمایش نوار زمان"

        scroll.isFillViewport = true
        val storyboardFrame = findViewById<View>(R.id.storyboardTableFrame)
        val storyboardMoveArea = findViewById<FrameLayout>(R.id.storyboardTableMoveArea)
        scroll.post {
            section.post {
                val fixedHeaderHeight = storyboardMoveArea.top.coerceAtLeast(0)
                val availableAreaHeight = (scroll.height - fixedHeaderHeight - dp(4)).coerceAtLeast(dp(120))
                storyboardMoveArea.layoutParams = storyboardMoveArea.layoutParams.apply { height = availableAreaHeight }
                storyboardFrame.layoutParams = (storyboardFrame.layoutParams as FrameLayout.LayoutParams).apply {
                    height = availableAreaHeight
                    width = storyboardMoveArea.width.takeIf { it > 0 } ?: scroll.width
                    gravity = Gravity.TOP
                }
                storyboardMoveArea.requestLayout()
                storyboardFrame.requestLayout()
                scroll.scrollTo(0, 0)
            }
        }
        if (!enabled) scroll.post { this@MainActivity.updateToolbarRailHeight() }
        findViewById<Button>(R.id.allViewButton).text = if (enabled) "بازگشت • All View" else "All View • فقط اسلایدها"
        scroll.post { scroll.scrollTo(0, 0) }
    }

    private fun buildEmptyStoryboard() {
        storyboardRows.removeAllViews()
        frameViews.clear()
        imageSearchFrameTimes.clear()
        val columns = storyboardColumns().coerceAtLeast(1)
        val cellHeight = storyboardCellHeight()
        val availableWidth = (storyboardRows.width.takeIf { it > 0 }
            ?: (resources.displayMetrics.widthPixels - dp(95)).coerceAtLeast(dp(150)))
        val cellWidth = (availableWidth / columns).coerceAtLeast(dp(32))
        val visibleIndices = (0 until activeStoryboardFrameCount).filter { it !in deletedStoryboardFrames }
        visibleIndices.chunked(columns).forEach { rowIndices ->
            val row = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
            }
            rowIndices.forEach { index ->
                val cell = makeFrameCell(index, null, "${index + 1}")
                val params = LinearLayout.LayoutParams(cellWidth, cellHeight).apply {
                    setMargins(0, 0, 0, 0)
                }
                row.addView(cell, params)
                frameViews[index] = cell
            }
            storyboardRows.addView(row)
        }
        refreshRailStoryboard()
        updateSelectionText()
    }

    private fun makeFrameCell(index: Int, bitmap: Bitmap?, label: String): FrameLayout {
        val cell = FrameLayout(this)
        cell.isFocusable = false
        cell.isFocusableInTouchMode = false
        cell.descendantFocusability = ViewGroup.FOCUS_BLOCK_DESCENDANTS
        cell.background = GradientDrawable().apply {
            setColor(Color.rgb(18, 35, 65)); cornerRadius = dp(2).toFloat()
        }
        val image = ImageView(this).apply {
            isFocusable = false
            isFocusableInTouchMode = false
            scaleType = ImageView.ScaleType.FIT_CENTER
            if (bitmap != null) setImageBitmap(bitmap) else setImageResource(android.R.drawable.ic_media_play)
            if (bitmap == null) setColorFilter(Color.rgb(116, 150, 198))
            contentDescription = "فریم ${index + 1}"
        }
        cell.addView(image, FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT))
        cell.isClickable = true
        cell.isFocusable = false
        cell.setOnTouchListener { _, event ->
            storyboardScaleDetector?.onTouchEvent(event)
            false
        }
        val labelHeight = dp(12)
        val timeLabel = TextView(this).apply {
            text = label; textSize = 8f; setTextColor(Color.WHITE)
            setPadding(dp(2), 0, dp(2), 0); gravity = Gravity.CENTER
            // Semi-transparent label: the thumbnail remains visible beneath it.
            setBackgroundColor(0x6607142F)
        }
        cell.addView(timeLabel, FrameLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, labelHeight, Gravity.BOTTOM or Gravity.START))
        val badge = TextView(this).apply {
            text = "✓"; textSize = 15f; setTextColor(Color.BLACK); gravity = Gravity.CENTER
            setBackgroundColor(Color.rgb(255, 210, 31)); visibility = View.GONE
        }
        val badgeParams = FrameLayout.LayoutParams(dp(22), dp(22), Gravity.TOP or Gravity.END)
        cell.addView(badge, badgeParams)
        cell.tag = badge
        cell.foreground = makeBorder(index in selectedFrames)
        badge.visibility = if (selectedCoverFrameIndex == index || index in selectedFrames) View.VISIBLE else View.GONE
        if (selectedCoverFrameIndex == index) { badge.text = "★"; badge.setBackgroundColor(Color.rgb(65, 220, 180)) }
        cell.setOnClickListener {
            if (selectedUri == null || videoDurationMs <= 0L) {
                Toast.makeText(this, "ابتدا یک ویدیو انتخاب کنید", Toast.LENGTH_SHORT).show()
                return@setOnClickListener
            }
            if (storyboardCoverMode) {
                selectedCoverFrameIndex = index
                refreshSelectionStyles()
                updateSelectionText()
                seekToStoryboardFrame(index)
                Toast.makeText(this, "فریم ${index + 1} برای کاور خروجی انتخاب شد", Toast.LENGTH_SHORT).show()
                return@setOnClickListener
            }
            if (!selectedFrames.add(index)) selectedFrames.remove(index)
            storyboardRangeAnchorIndex = index
            refreshSelectionStyles()
            updateSelectionText()
            seekToStoryboardFrame(index)
        }
        cell.setOnLongClickListener {
            if (selectedUri == null || videoDurationMs <= 0L) {
                Toast.makeText(this, "ابتدا یک ویدیو انتخاب کنید", Toast.LENGTH_SHORT).show()
                return@setOnLongClickListener true
            }
            if (index in selectedFrames) {
                selectedFrames.remove(index)
                if (storyboardRangeAnchorIndex == index) storyboardRangeAnchorIndex = null
                refreshSelectionStyles()
                updateSelectionText()
                seekToStoryboardFrame(index)
                Toast.makeText(this, "فریم ${index + 1} از انتخاب گروهی خارج شد", Toast.LENGTH_SHORT).show()
                return@setOnLongClickListener true
            }
            val anchor = storyboardRangeAnchorIndex
            if (anchor == null) {
                storyboardRangeAnchorIndex = index
                Toast.makeText(this, "ابتدا یک اسلاید را لمس کنید، سپس اسلاید مقصد را نگه دارید", Toast.LENGTH_SHORT).show()
            } else {
                val first = minOf(anchor, index)
                val last = maxOf(anchor, index)
                for (frameIndex in first..last) {
                    if (frameIndex in deletedStoryboardFrames || frameIndex !in frameViews) continue
                    selectedFrames.add(frameIndex)
                }
                // The long-pressed cell becomes the next range anchor.
                storyboardRangeAnchorIndex = index
                refreshSelectionStyles()
                updateSelectionText()
                seekToStoryboardFrame(index)
            }
            true
        }
        cell.setOnDragListener { _, event ->
            if (event.action == android.view.DragEvent.ACTION_DROP) {
                seekToStoryboardFrame(index)
                selectedFrames.clear()
                selectedFrames.add(index)
                updateSelectionText()
                refreshSelectionStyles()
                statusText.text = "فریم ${index + 1} به بخش ویرایش منتقل شد و روی پلیر فعال است"
                true
            } else event.action == android.view.DragEvent.ACTION_DRAG_STARTED
        }
        // A selected storyboard frame can be long-pressed again and dragged to an editor area.
        return cell
    }

    private fun seekToStoryboardFrame(index: Int) {
        val rangeStart = storyboardStartMs.coerceIn(0L, videoDurationMs)
        val rangeEnd = (if (storyboardEndMs > rangeStart) storyboardEndMs else videoDurationMs).coerceIn(rangeStart, videoDurationMs)
        val timeMs = storyboardTimestampForIndex(index, activeStoryboardFrameCount, rangeStart, rangeEnd)
        timelineView.setPlayhead(timeMs)
        try { videoView.seekTo(timeMs.toInt()) } catch (_: Exception) { }
    }

    private fun makeBorder(selected: Boolean): GradientDrawable = GradientDrawable().apply {
        setColor(Color.TRANSPARENT)
        cornerRadius = dp(2).toFloat()
        setStroke(dp(if (selected) 3 else 1), if (selected) Color.rgb(255, 210, 31) else Color.rgb(61, 91, 135))
    }

    /** Returns the timestamp represented by a storyboard cell. Blank interval keeps the automatic spacing. */
    private fun storyboardTimestampForIndex(index: Int, count: Int, startMs: Long, endMs: Long): Long {
        imageSearchFrameTimes[index]?.let { return it.coerceIn(startMs, endMs) }
        val interval = storyboardIntervalMs
        return if (interval != null && interval > 0L) {
            startMs + index.toLong() * interval
        } else if (count <= 1) startMs else startMs + (endMs - startMs) * index / count
    }

    private fun loadStoryboard(uri: Uri) {
        val generation = ++storyboardGeneration
        val countForThisLoad = activeStoryboardFrameCount
        val initialVisibleIndex = run {
            val scroll = findViewById<ScrollView>(R.id.storyboardTableScroll)
            val rows = findViewById<LinearLayout>(R.id.storyboardRows)
            val columns = storyboardColumns().coerceAtLeast(1)
            val visibleTop = scroll.scrollY
            val firstRow = (0 until rows.childCount).firstOrNull { r -> rows.getChildAt(r).bottom > visibleTop } ?: 0
            (firstRow * columns).coerceIn(0, (countForThisLoad - 1).coerceAtLeast(0))
        }
        storyboardPriorityIndex = initialVisibleIndex
        worker.execute {
            var metadataRetriever: MediaMetadataRetriever? = null
            try {
                metadataRetriever = MediaMetadataRetriever()
                metadataRetriever.setDataSource(this, uri)
                val duration = metadataRetriever.extractMetadata(MediaMetadataRetriever.METADATA_KEY_DURATION)?.toLongOrNull() ?: 0L
                try { metadataRetriever.release() } catch (_: Exception) { }
                metadataRetriever = null

                mainHandler.post {
                    if (generation != storyboardGeneration) return@post
                    videoDurationMs = duration
                    findViewById<EditText>(R.id.overlayTextEndTime).setText(formatTime(duration))
                    findViewById<EditText>(R.id.overlayVideoEndTime).setText(formatTime(duration))
                    updateLiveTextPreview()
                    if (storyboardEndMs <= storyboardStartMs || storyboardEndMs > duration) {
                        storyboardStartMs = 0L
                        storyboardEndMs = duration
                        suppressStoryboardAutoApply = true
                        try {
                            findViewById<android.widget.EditText>(R.id.storyboardStartTime).setText("00:00")
                            findViewById<android.widget.EditText>(R.id.storyboardEndTime).setText(formatTime(duration))
                        } finally { suppressStoryboardAutoApply = false }
                    }
                    timelineView.setTimeline(duration, timelineSplitPoints.toList(), deletedTimelineRanges)
                    trackTimelineView.setClips(trackClips.toList(), duration)
                    statusText.text = if (duration > 0) "مدت ویدیو ${formatTime(duration)} • در حال استخراج فریم‌ها…" else "در حال استخراج فریم‌ها…"
                }

                val count = countForThisLoad
                val rangeStart = storyboardStartMs.coerceIn(0L, duration)
                val rangeEnd = (if (storyboardEndMs > rangeStart) storyboardEndMs else duration).coerceIn(rangeStart, duration)
                val preferred = initialVisibleIndex.coerceIn(0, (count - 1).coerceAtLeast(0))
                val orderedIndices = (0 until count).sortedBy { candidate ->
                    (candidate - preferred + count) % count.coerceAtLeast(1)
                }
                val workerCount = 2
                val completedWorkers = java.util.concurrent.atomic.AtomicInteger(0)
                repeat(workerCount) { workerIndex ->
                    val assigned = orderedIndices.filterIndexed { order, _ -> order % workerCount == workerIndex }
                    storyboardFrameWorkers.execute {
                        var frameRetriever: MediaMetadataRetriever? = null
                        try {
                            frameRetriever = MediaMetadataRetriever()
                            frameRetriever.setDataSource(this, uri)
                            for (index in assigned) {
                                if (generation != storyboardGeneration) break
                                if (index in deletedStoryboardFrames) continue
                                val timestampMs = storyboardTimestampForIndex(index, count, rangeStart, rangeEnd)
                                if (timestampMs >= rangeEnd) continue
                                val bitmap: Bitmap? = try {
                                    if (android.os.Build.VERSION.SDK_INT >= 27) {
                                        frameRetriever.getScaledFrameAtTime(timestampMs * 1000L, MediaMetadataRetriever.OPTION_CLOSEST_SYNC, 144, 90)
                                    } else {
                                        frameRetriever.getFrameAtTime(timestampMs * 1000L, MediaMetadataRetriever.OPTION_CLOSEST_SYNC)
                                    }
                                } catch (_: Exception) { null }
                                if (bitmap != null) {
                                    val scaled = if (bitmap.width <= 144 && bitmap.height <= 90) bitmap
                                        else scaleBitmapPreservingAspect(bitmap, 144, 90)
                                    mainHandler.post {
                                        if (generation == storyboardGeneration) {
                                            frameBitmaps[index] = scaled
                                            val cell = frameViews[index]
                                            val image = cell?.getChildAt(0) as? ImageView
                                            image?.setImageBitmap(scaled)
                                            image?.clearColorFilter()
                                            (cell?.getChildAt(1) as? TextView)?.text = formatTime(timestampMs)
                                            cell?.visibility = if (index in deletedStoryboardFrames) View.GONE else View.VISIBLE
                                        } else if (!scaled.isRecycled) scaled.recycle()
                                    }
                                }
                            }
                        } catch (_: Exception) {
                            // A failed decoder shard must not prevent the remaining shards from completing.
                        } finally {
                            try { frameRetriever?.release() } catch (_: Exception) { }
                            if (completedWorkers.incrementAndGet() == workerCount) {
                                mainHandler.post {
                                    if (generation == storyboardGeneration) {
                                        statusText.text = "استوری‌بورد آماده است: $activeStoryboardFrameCount اسلاید"
                                        // Start the secondary timeline strip only after storyboard
                                        // decoding finishes, so it cannot compete for decoders.
                                        loadTimelineThumbnails(uri, duration, generation)
                                    }
                                }
                            }
                        }
                    }
                }
            } catch (_: Exception) {
                mainHandler.post { if (generation == storyboardGeneration) statusText.text = "استخراج فریم‌ها ناموفق بود؛ پخش ویدیو همچنان در دسترس است" }
            } finally { try { metadataRetriever?.release() } catch (_: Exception) { } }
        }
    }

    /** Samples a compact strip independently from the slower 120-frame storyboard. */
    private fun loadTimelineThumbnails(uri: Uri, durationMs: Long, generation: Int) {
        timelineThumbnailWorker.execute {
            var retriever: MediaMetadataRetriever? = null
            val frames = mutableListOf<Pair<Long, Bitmap>>()
            try {
                retriever = MediaMetadataRetriever()
                retriever.setDataSource(this, uri)
                val sampleCount = 24
                for (i in 0 until sampleCount) {
                    if (generation != storyboardGeneration) break
                    val time = if (sampleCount <= 1) 0L else durationMs * i / sampleCount
                    val bitmap = try {
                        if (android.os.Build.VERSION.SDK_INT >= 27) {
                            retriever.getScaledFrameAtTime(time * 1000L, MediaMetadataRetriever.OPTION_CLOSEST_SYNC, 160, 90)
                        } else {
                            retriever.getFrameAtTime(time * 1000L, MediaMetadataRetriever.OPTION_CLOSEST_SYNC)
                        }
                    } catch (_: Exception) { null }
                    if (bitmap != null) frames.add(time to scaleBitmapPreservingAspect(bitmap, 160, 90))
                }
                mainHandler.post {
                    if (generation == storyboardGeneration) {
                        timelineView.setThumbnails(frames)
                    } else frames.forEach { if (!it.second.isRecycled) it.second.recycle() }
                }
            } catch (_: Exception) {
                frames.forEach { if (!it.second.isRecycled) it.second.recycle() }
            } finally { try { retriever?.release() } catch (_: Exception) { } }
        }
    }

    private fun showTimeMode() {
        storyboardStartMs = 0L
        storyboardEndMs = videoDurationMs
        storyboardIntervalMs = null
        activeStoryboardFrameCount = DEFAULT_STORYBOARD_FRAME_COUNT
        cleanupTemporaryStoryboardCells()
        selectedFrames.clear()
        storyboardRangeAnchorIndex = null
        suppressStoryboardAutoApply = true
        try {
            findViewById<EditText>(R.id.storyboardIntervalTime).setText("")
            findViewById<android.widget.EditText>(R.id.storyboardStartTime).setText("00:00")
            findViewById<android.widget.EditText>(R.id.storyboardEndTime).setText(formatTime(videoDurationMs))
        } finally { suppressStoryboardAutoApply = false }
        frameViews.forEach { (index, view) -> view.visibility = if (index in deletedStoryboardFrames) View.GONE else View.VISIBLE }
        updateModeButtons()
        val uri = selectedUri
        if (uri != null && videoDurationMs > 0L) reloadStoryboardForRange(uri)
        statusText.text = "نمایش زمانی کامل: از 00:00 تا ${formatTime(videoDurationMs)}"
    }

    private fun parseTimeInput(value: String): Long? {
        val text = value.trim()
        if (text.isEmpty()) return null
        return try {
            val parts = text.split(":")
            val seconds = when (parts.size) {
                1 -> parts[0].toLong()
                2 -> parts[0].toLong() * 60L + parts[1].toLong()
                3 -> parts[0].toLong() * 3600L + parts[1].toLong() * 60L + parts[2].toLong()
                else -> return null
            }
            if (parts.any { it.toLongOrNull() == null } || seconds < 0L) null else seconds * 1000L
        } catch (_: Exception) { null }
    }

    /** Sets the storyboard range endpoint to the current playback position without opening a dialog. */
    private fun setStoryboardTimeFromPlayback(isStart: Boolean) {
        if (selectedUri == null || videoDurationMs <= 0L) {
            Toast.makeText(this, "ابتدا ویدیو را انتخاب کنید", Toast.LENGTH_SHORT).show()
            return
        }
        val position = try { videoView.currentPosition.toLong() } catch (_: Exception) { timelineView.playheadMs }
        val at = position.coerceIn(0L, videoDurationMs)
        val fieldId = if (isStart) R.id.storyboardStartTime else R.id.storyboardEndTime
        findViewById<android.widget.EditText>(fieldId).apply {
            setText(formatTime(at))
            error = null
        }
        statusText.text = if (isStart) {
            "زمان شروع استوری‌بورد روی ${formatTime(at)} ثبت شد؛ پس از دو ثانیه، استوری‌بورد خودکار به‌روزرسانی می‌شود"
        } else {
            "زمان پایان استوری‌بورد روی ${formatTime(at)} ثبت شد؛ پس از دو ثانیه، استوری‌بورد خودکار به‌روزرسانی می‌شود"
        }
    }

    private fun applyStoryboardTimeRange() {
        mainHandler.removeCallbacks(storyboardAutoApplyRunnable)
        val uri = selectedUri
        if (uri == null || videoDurationMs <= 0L) {
            Toast.makeText(this, "ابتدا ویدیو را انتخاب کنید", Toast.LENGTH_SHORT).show(); return
        }
        val start = parseTimeInput(findViewById<android.widget.EditText>(R.id.storyboardStartTime).text.toString())
        val end = parseTimeInput(findViewById<android.widget.EditText>(R.id.storyboardEndTime).text.toString())
        val intervalField = findViewById<android.widget.EditText>(R.id.storyboardIntervalTime)
        val intervalText = intervalField.text.toString().trim()
        val interval = if (intervalText.isEmpty()) null else parseTimeInput(intervalText)
        if (start == null || end == null || start >= end || end > videoDurationMs) {
            findViewById<android.widget.EditText>(R.id.storyboardEndTime).error = "زمان پایان باید بعد از شروع و در محدودهٔ ویدیو باشد"
            Toast.makeText(this, "زمان شروع و پایان را به‌شکل دقیقه:ثانیه وارد کنید؛ مثلاً 01:25", Toast.LENGTH_LONG).show(); return
        }
        if (intervalText.isNotEmpty() && (interval == null || interval <= 0L)) {
            intervalField.error = "مثلاً 10 برای 10 ثانیه یا 01:30 برای یک دقیقه و نیم"
            Toast.makeText(this, "فاصله را به ثانیه یا دقیقه:ثانیه وارد کنید", Toast.LENGTH_LONG).show(); return
        }
        intervalField.error = null
        storyboardStartMs = start
        storyboardEndMs = end
        val rangeLength = end - start
        if (interval == null) {
            // Returning to automatic spacing removes any temporary extra storyboard cells.
            storyboardIntervalMs = null
            activeStoryboardFrameCount = DEFAULT_STORYBOARD_FRAME_COUNT
            cleanupTemporaryStoryboardCells()
        } else {
            val requestedCount = ((rangeLength + interval - 1L) / interval).coerceAtLeast(1L)
            activeStoryboardFrameCount = requestedCount.coerceAtMost(MAX_STORYBOARD_FRAME_COUNT.toLong()).toInt()
            // If a tiny interval would require an impractically large grid, widen it slightly
            // so the final cell still reaches the end of the requested video range.
            val effectiveInterval = if (requestedCount > MAX_STORYBOARD_FRAME_COUNT) {
                (rangeLength + activeStoryboardFrameCount - 1L) / activeStoryboardFrameCount
            } else interval
            storyboardIntervalMs = effectiveInterval
            if (effectiveInterval != interval) {
                suppressStoryboardAutoApply = true
                try { intervalField.setText(formatTime(effectiveInterval)) }
                finally { suppressStoryboardAutoApply = false }
                Toast.makeText(this, "برای نمایش کامل ویدیو، فاصله به ${formatTime(effectiveInterval)} تنظیم شد تا تعداد اسلایدها از $MAX_STORYBOARD_FRAME_COUNT بیشتر نشود", Toast.LENGTH_LONG).show()
            }
        }
        selectedFrames.clear()
        storyboardRangeAnchorIndex = null
        reloadStoryboardForRange(uri)
        statusText.text = if (interval == null) "استوری‌بورد بازهٔ ${formatTime(start)} تا ${formatTime(end)} با فاصلهٔ خودکار آماده می‌شود؛ اسلایدهای موقت قبلی حذف می‌شوند" else "در حال ساخت ${activeStoryboardFrameCount} اسلاید برای پوشش کامل بازهٔ ${formatTime(start)} تا ${formatTime(end)}…"
    }

    /** After a completed export, discard temporary interval-only cells and restore the normal 120-cell storyboard. */
    private fun restoreNormalStoryboardAfterExport() {
        val uri = selectedUri ?: return
        if (activeStoryboardFrameCount <= DEFAULT_STORYBOARD_FRAME_COUNT && storyboardIntervalMs == null &&
            storyboardStartMs == 0L && storyboardEndMs == videoDurationMs) return
        storyboardStartMs = 0L
        storyboardEndMs = videoDurationMs
        storyboardIntervalMs = null
        activeStoryboardFrameCount = DEFAULT_STORYBOARD_FRAME_COUNT
        selectedFrames.clear()
        storyboardRangeAnchorIndex = null
        cleanupTemporaryStoryboardCells()
        suppressStoryboardAutoApply = true
        try {
            findViewById<EditText>(R.id.storyboardIntervalTime).setText("")
            findViewById<EditText>(R.id.storyboardStartTime).setText("00:00")
            findViewById<EditText>(R.id.storyboardEndTime).setText(formatTime(videoDurationMs))
        } finally { suppressStoryboardAutoApply = false }
        reloadStoryboardForRange(uri)
        updateSelectionText()
    }

    /** Forget per-cell state belonging to temporary cells once the grid returns to its base size. */
    private fun cleanupTemporaryStoryboardCells() {
        selectedFrames.removeAll { it >= DEFAULT_STORYBOARD_FRAME_COUNT }
        deletedStoryboardFrames.removeAll { it >= DEFAULT_STORYBOARD_FRAME_COUNT }
        frameColorProfiles.keys.removeAll { it >= DEFAULT_STORYBOARD_FRAME_COUNT }
        imageSearchFrameTimes.keys.removeAll { it >= DEFAULT_STORYBOARD_FRAME_COUNT }
    }

    private fun reloadStoryboardForRange(uri: Uri) {
        val storyboardScroll = findViewById<ScrollView>(R.id.storyboardTableScroll)
        val previousScrollY = storyboardScroll.scrollY
        imageSearchFrameTimes.clear()
        frameBitmaps.values.forEach { if (!it.isRecycled) it.recycle() }
        frameBitmaps.clear()
        // Rebuild the grid to match the newly computed cell count. Any temporary
        // extra cells from the previous custom interval disappear here.
        buildEmptyStoryboard()
        storyboardScroll.post { storyboardScroll.scrollTo(0, previousScrollY.coerceAtMost((storyboardScroll.getChildAt(0)?.height ?: 0) - storyboardScroll.height).coerceAtLeast(0)) }
        timelineView.setThumbnails(emptyList())
        previewBitmaps.values.forEach { if (!it.isRecycled) it.recycle() }
        previewBitmaps.clear()
        loadStoryboard(uri)
    }

    private fun scaleBitmapPreservingAspect(source: Bitmap, maxWidth: Int = 160, maxHeight: Int = 100): Bitmap {
        val scale = minOf(maxWidth.toFloat() / source.width, maxHeight.toFloat() / source.height, 1f)
        val width = (source.width * scale).toInt().coerceAtLeast(1)
        val height = (source.height * scale).toInt().coerceAtLeast(1)
        if (width == source.width && height == source.height) return source
        return Bitmap.createScaledBitmap(source, width, height, true).also { if (it !== source && !source.isRecycled) source.recycle() }
    }

    /** Reflow visible storyboard frames into fixed-column rows without changing their widths. */
    private fun rebuildStoryboardRowsPreservingFrames() {
        storyboardRows.removeAllViews()
        frameViews.clear()
        val columns = storyboardColumns().coerceAtLeast(1)
        val cellHeight = storyboardCellHeight()
        val visibleIndices = (0 until activeStoryboardFrameCount).filter { it !in deletedStoryboardFrames }
        val availableWidth = (storyboardRows.width.takeIf { it > 0 }
            ?: (resources.displayMetrics.widthPixels - dp(95)).coerceAtLeast(dp(150)))
        val cellWidth = (availableWidth / columns).coerceAtLeast(dp(32))
        visibleIndices.chunked(columns).forEach { rowIndices ->
            val row = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
            }
            rowIndices.forEach { index ->
                val bitmap = frameBitmaps[index]
                val label = imageSearchFrameTimes[index]?.let { formatTime(it) } ?: "${index + 1}"
                val cell = makeFrameCell(index, bitmap, label)
                row.addView(cell, LinearLayout.LayoutParams(cellWidth, cellHeight).apply { setMargins(0, 0, 0, 0) })
                frameViews[index] = cell
            }
            storyboardRows.addView(row)
        }
        storyboardRows.requestLayout()
        refreshRailStoryboard()
    }

    private fun deleteSelectedStoryboardFrames() {
        recordUndoState()
        if (selectedFrames.isEmpty()) {
            Toast.makeText(this, "ابتدا فریم‌هایی را انتخاب کنید", Toast.LENGTH_SHORT).show()
            return
        }
        val toDelete = selectedFrames.toList()
        toDelete.forEach { index -> deletedStoryboardFrames.add(index) }
        selectedFrames.clear()
        // Rebuild complete rows after deletion. Removing individual cells leaves short
        // rows with fewer weighted children, which makes their remaining cells expand.
        rebuildStoryboardRowsPreservingFrames()
        updateSelectionText()
        statusText.text = "${toDelete.size} بازهٔ زمانی برای حذف از خروجی علامت‌گذاری شد"
        Toast.makeText(this, "بازه‌های زمانی این اسلایدها از ویدیوی خروجی حذف می‌شوند؛ فایل اصلی دست‌نخورده می‌ماند", Toast.LENGTH_LONG).show()
    }


    /** Saves every Cut-delimited timeline interval as its own file, stream-copying tracks without re-encoding. */
    /** Writes a MediaInfo-style sidecar report from the actual saved output file. */
    private fun writeOutputInfoReport(videoUri: Uri) {
        try {
            val displayName = contentResolver.query(videoUri, arrayOf(MediaStore.MediaColumns.DISPLAY_NAME), null, null, null)?.use { c ->
                if (c.moveToFirst()) c.getString(0) else null
            } ?: "EVC_output.mp4"
            val size = contentResolver.openAssetFileDescriptor(videoUri, "r")?.use { it.length } ?: -1L
            val retriever = MediaMetadataRetriever()
            retriever.setDataSource(this, videoUri)
            fun meta(key: Int): String = retriever.extractMetadata(key)?.takeIf { it.isNotBlank() } ?: "Not available"
            val duration = meta(MediaMetadataRetriever.METADATA_KEY_DURATION).toLongOrNull()?.let { "${it} ms" } ?: "Not available"
            val width = meta(MediaMetadataRetriever.METADATA_KEY_VIDEO_WIDTH)
            val height = meta(MediaMetadataRetriever.METADATA_KEY_VIDEO_HEIGHT)
            val frameRate = meta(MediaMetadataRetriever.METADATA_KEY_CAPTURE_FRAMERATE)
            val date = meta(MediaMetadataRetriever.METADATA_KEY_DATE)
            val extractor = MediaExtractor()
            extractor.setDataSource(this, videoUri, null)
            val report = StringBuilder()
            report.append("General\nComplete name : ").append(displayName).append("\nFormat : ").append(if (displayName.endsWith(".mkv", true)) "Matroska (MKV)" else "MP4 container").append("\nFile size : ")
                .append(if (size >= 0) String.format(java.util.Locale.US, "%.2f KiB", size / 1024.0) else "Not available")
                .append("\nDuration : ").append(duration).append("\nEncoded date : ").append(date).append("\n\n")
            var videoIndex = 0
            var audioIndex = 0
            for (i in 0 until extractor.trackCount) {
                val f = extractor.getTrackFormat(i)
                val mime = f.getString(MediaFormat.KEY_MIME) ?: "Not available"
                if (mime.startsWith("video/")) {
                    videoIndex++
                    report.append("Video #").append(videoIndex).append("\nFormat : ").append(mime).append("\nCodec ID : ").append(mime)
                    report.append("\nWidth : ").append(if (f.containsKey(MediaFormat.KEY_WIDTH)) f.getInteger(MediaFormat.KEY_WIDTH) else width).append(" pixels")
                    report.append("\nHeight : ").append(if (f.containsKey(MediaFormat.KEY_HEIGHT)) f.getInteger(MediaFormat.KEY_HEIGHT) else height).append(" pixels")
                    if (f.containsKey(MediaFormat.KEY_FRAME_RATE)) report.append("\nFrame rate : ").append(f.getInteger(MediaFormat.KEY_FRAME_RATE)).append(" FPS") else report.append("\nFrame rate : ").append(frameRate)
                    report.append("\nBit rate : ").append(if (f.containsKey(MediaFormat.KEY_BIT_RATE)) "${f.getInteger(MediaFormat.KEY_BIT_RATE)} b/s" else "Not available")
                    report.append("\nProfile : ").append(if (f.containsKey(MediaFormat.KEY_PROFILE)) f.getInteger(MediaFormat.KEY_PROFILE) else "Not available")
                    report.append("\nColor format : ").append(if (f.containsKey(MediaFormat.KEY_COLOR_FORMAT)) f.getInteger(MediaFormat.KEY_COLOR_FORMAT) else "Not available").append("\n\n")
                } else if (mime.startsWith("audio/")) {
                    audioIndex++
                    report.append("Audio #").append(audioIndex).append("\nFormat : ").append(mime).append("\nCodec ID : ").append(mime)
                    report.append("\nBit rate : ").append(if (f.containsKey(MediaFormat.KEY_BIT_RATE)) "${f.getInteger(MediaFormat.KEY_BIT_RATE)} b/s" else "Not available")
                    report.append("\nSampling rate : ").append(if (f.containsKey(MediaFormat.KEY_SAMPLE_RATE)) "${f.getInteger(MediaFormat.KEY_SAMPLE_RATE)} Hz" else "Not available")
                    report.append("\nChannel(s) : ").append(if (f.containsKey(MediaFormat.KEY_CHANNEL_COUNT)) f.getInteger(MediaFormat.KEY_CHANNEL_COUNT) else "Not available")
                    report.append("\nLanguage : ").append(if (f.containsKey(MediaFormat.KEY_LANGUAGE)) f.getString(MediaFormat.KEY_LANGUAGE) else "Not available").append("\n\n")
                }
            }
            extractor.release(); retriever.release()
            val values = ContentValues().apply {
                put(MediaStore.MediaColumns.DISPLAY_NAME, displayName.substringBeforeLast('.', displayName) + "_Info.txt")
                put(MediaStore.MediaColumns.MIME_TYPE, "text/plain")
                if (android.os.Build.VERSION.SDK_INT >= 29) {
                    put(MediaStore.MediaColumns.RELATIVE_PATH, Environment.DIRECTORY_DOWNLOADS + "/EVC_Info")
                    put(MediaStore.MediaColumns.IS_PENDING, 1)
                }
            }
            val reportUri = contentResolver.insert(MediaStore.Downloads.EXTERNAL_CONTENT_URI, values) ?: return
            contentResolver.openOutputStream(reportUri)?.bufferedWriter(Charsets.UTF_8)?.use { it.write(report.toString()) }
            if (android.os.Build.VERSION.SDK_INT >= 29) contentResolver.update(reportUri, ContentValues().apply { put(MediaStore.MediaColumns.IS_PENDING, 0) }, null, null)
        } catch (_: Exception) { /* Report failure must not invalidate a successfully exported video. */ }
    }

    /** Exports the timeline edit (cut points + deleted ranges) as one continuous video.
     *  This path is intentionally independent of storyboard frame selection.
     */
    private fun exportTimelineEditedVideo() {
        val source = selectedUri
        if (source == null || videoDurationMs <= 0L) {
            Toast.makeText(this, "ابتدا یک ویدیوی معتبر انتخاب کنید", Toast.LENGTH_SHORT).show()
            return
        }
        val deleted = synchronized(deletedTimelineRanges) { deletedTimelineRanges.toList() }
            .map { it.first.coerceIn(0L, videoDurationMs) to it.second.coerceIn(0L, videoDurationMs) }
            .filter { it.second > it.first }
            .sortedBy { it.first }
        val mergedDeleted = deleted.fold(mutableListOf<Pair<Long, Long>>()) { acc, range ->
            if (acc.isNotEmpty() && range.first <= acc.last().second) {
                val previous = acc.removeAt(acc.lastIndex)
                acc.add(previous.first to max(previous.second, range.second))
            } else acc.add(range)
            acc
        }
        val keptRanges = mutableListOf<Pair<Long, Long>>()
        var cursor = 0L
        for (range in mergedDeleted) {
            if (range.first > cursor) keptRanges.add(cursor to range.first)
            cursor = max(cursor, range.second)
        }
        if (cursor < videoDurationMs) keptRanges.add(cursor to videoDurationMs)
        if (keptRanges.isEmpty()) {
            Toast.makeText(this, "تمام بخش‌های نوار زمان حذف شده‌اند؛ چیزی برای خروجی باقی نمانده است", Toast.LENGTH_LONG).show()
            return
        }
        val button = findViewById<Button>(R.id.outputChangesButton)
        button.isEnabled = false
        statusText.text = "در حال ساخت یک خروجی از بخش‌های باقی‌ماندهٔ نوار زمان، بدون رمزگذاری مجدد…"
        worker.execute {
            var result: File? = null
            var error: String? = null
            try { result = muxRemainingRanges(source, keptRanges) }
            catch (e: Exception) { error = e.message ?: e.javaClass.simpleName }
            mainHandler.post {
                button.isEnabled = true
                val file = result
                if (file == null || !file.exists() || file.length() == 0L) {
                    statusText.text = "خروجی ویرایش نوار زمان ناموفق بود: ${error ?: "خطای ناشناخته"}"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                    file?.delete()
                    return@post
                }
                try {
                    val values = ContentValues().apply {
                        put(MediaStore.Video.Media.DISPLAY_NAME, requestedOutputDisplayName("EVC_timeline_edited_${System.currentTimeMillis()}", outputExtension()))
                        put(MediaStore.Video.Media.MIME_TYPE, outputMimeType())
                        if (android.os.Build.VERSION.SDK_INT >= 29) {
                            put(MediaStore.Video.Media.RELATIVE_PATH, Environment.DIRECTORY_MOVIES + "/EVC")
                            put(MediaStore.Video.Media.IS_PENDING, 1)
                        }
                    }
                    val outUri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
                        ?: throw IllegalStateException("ساخت فایل خروجی ممکن نشد")
                    contentResolver.openOutputStream(outUri)?.use { out -> FileInputStream(file).use { it.copyTo(out) } }
                        ?: throw IllegalStateException("نوشتن فایل خروجی ناموفق بود")
                    if (android.os.Build.VERSION.SDK_INT >= 29) contentResolver.update(outUri, ContentValues().apply { put(MediaStore.Video.Media.IS_PENDING, 0) }, null, null)
                    writeOutputInfoReport(outUri)
                    file.delete()
                    restoreNormalStoryboardAfterExport()
                    statusText.text = "خروجی نوار زمان در Movies/EVC ذخیره شد؛ بخش‌های حذف‌شده کنار گذاشته شدند و استوری‌بورد دخالتی نداشت."
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                } catch (e: Exception) {
                    file.delete()
                    statusText.text = "ذخیرهٔ خروجی ناموفق بود: ${e.message ?: "خطا"}"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                }
            }
        }
    }

    private fun exportTimelineSegmentsSeparately() {
        val source = selectedUri
        if (source == null || videoDurationMs <= 0L) {
            Toast.makeText(this, "ابتدا یک ویدیوی معتبر انتخاب کنید", Toast.LENGTH_SHORT).show()
            return
        }
        val boundaries = (listOf(0L) + timelineSplitPoints.filter { it > 0L && it < videoDurationMs } + listOf(videoDurationMs)).distinct().sorted()
        if (boundaries.size < 2) {
            Toast.makeText(this, "ابتدا با دکمهٔ Cut نقاط تقسیم را روی نوار زمان ثبت کنید", Toast.LENGTH_LONG).show()
            return
        }
        val deleted = synchronized(deletedTimelineRanges) { deletedTimelineRanges.toList() }
        val segments = (0 until boundaries.size - 1).map { boundaries[it] to boundaries[it + 1] }
            .filter { (a, b) -> b > a && deleted.none { d -> d.first <= a && d.second >= b } }
        if (segments.isEmpty()) {
            Toast.makeText(this, "قطعهٔ قابل ذخیره‌ای باقی نمانده است", Toast.LENGTH_LONG).show()
            return
        }
        val button = findViewById<Button>(R.id.outputChangesButton)
        button.isEnabled = false
        statusText.text = "در حال ذخیرهٔ ${segments.size} قطعه به‌صورت فایل‌های جداگانه و بدون رمزگذاری مجدد…"
        worker.execute {
            var saved = 0
            val errors = mutableListOf<String>()
            segments.forEachIndexed { index, range ->
                var temp: File? = null
                var outUri: Uri? = null
                try {
                    temp = muxRemainingRanges(source, listOf(range))
                    val values = ContentValues().apply {
                        put(MediaStore.Video.Media.DISPLAY_NAME, requestedOutputDisplayName("EVC_segment_${(index + 1).toString().padStart(3, '0')}_${System.currentTimeMillis()}", outputExtension()))
                        put(MediaStore.Video.Media.MIME_TYPE, outputMimeType())
                        if (android.os.Build.VERSION.SDK_INT >= 29) {
                            put(MediaStore.Video.Media.RELATIVE_PATH, Environment.DIRECTORY_MOVIES + "/EVC")
                            put(MediaStore.Video.Media.IS_PENDING, 1)
                        }
                    }
                    outUri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
                        ?: throw IllegalStateException("ساخت فایل قطعهٔ ${index + 1} ناموفق بود")
                    contentResolver.openOutputStream(outUri)?.use { output -> FileInputStream(temp).use { input -> input.copyTo(output) } }
                        ?: throw IllegalStateException("نوشتن قطعهٔ ${index + 1} ناموفق بود")
                    if (android.os.Build.VERSION.SDK_INT >= 29) {
                        val done = ContentValues().apply { put(MediaStore.Video.Media.IS_PENDING, 0) }
                        contentResolver.update(outUri, done, null, null)
                    }
                    writeOutputInfoReport(outUri!!)
                    saved++
                } catch (e: Exception) {
                    outUri?.let { try { contentResolver.delete(it, null, null) } catch (_: Exception) { } }
                    errors.add("قطعهٔ ${index + 1}: ${e.message ?: e.javaClass.simpleName}")
                } finally {
                    temp?.delete()
                }
            }
            mainHandler.post {
                button.isEnabled = true
                statusText.text = if (errors.isEmpty()) "$saved قطعه به‌صورت فایل‌های جداگانه در Movies/EVC ذخیره شد؛ بدون رمزگذاری مجدد" else "$saved قطعه ذخیره شد؛ ${errors.size} قطعه ناموفق بود: ${errors.first()}"
                Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
            }
        }
    }


    private fun installPlayerResizeHandle() {
        val handle = findViewById<View>(R.id.playerResizeHandle)
        val playerRow = findViewById<View>(R.id.playerActionRow)
        var startY = 0f
        var startHeight = 0
        handle.setOnTouchListener { _, event ->
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    startY = event.rawY
                    startHeight = playerRow.layoutParams.height
                    true
                }
                MotionEvent.ACTION_MOVE -> {
                    val delta = (event.rawY - startY).toInt()
                    val maxHeight = (resources.displayMetrics.heightPixels * 0.72f).toInt()
                    val newHeight = (startHeight + delta).coerceIn(dp(170), maxHeight.coerceAtLeast(dp(240)))
                    if (newHeight != playerRow.layoutParams.height) {
                        playerRow.layoutParams = playerRow.layoutParams.apply { height = newHeight }
                    }
                    true
                }
                MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                    handle.performClick()
                    true
                }
                else -> true
            }
        }
    }

    private fun showVideoInfoDialog() {
        val uri = selectedUri
        if (uri == null) {
            android.widget.Toast.makeText(this, "ابتدا یک ویدیو انتخاب کنید", android.widget.Toast.LENGTH_SHORT).show()
            return
        }
        statusText.text = "در حال خواندن اطلاعات ویدیو…"
        worker.execute {
            val lines = mutableListOf<String>()
            var retriever: MediaMetadataRetriever? = null
            var extractor: MediaExtractor? = null
            try {
                retriever = MediaMetadataRetriever().apply { setDataSource(this@MainActivity, uri) }
                fun meta(key: Int): String = retriever?.extractMetadata(key)?.takeIf { it.isNotBlank() } ?: "نامشخص"
                var fileName = uri.lastPathSegment ?: "نامشخص"
                var fileSize = -1L
                try {
                    contentResolver.query(uri, arrayOf(OpenableColumns.DISPLAY_NAME, OpenableColumns.SIZE), null, null, null)?.use { c ->
                        if (c.moveToFirst()) {
                            val nameIndex = c.getColumnIndex(OpenableColumns.DISPLAY_NAME)
                            val sizeIndex = c.getColumnIndex(OpenableColumns.SIZE)
                            if (nameIndex >= 0) fileName = c.getString(nameIndex) ?: fileName
                            if (sizeIndex >= 0 && !c.isNull(sizeIndex)) fileSize = c.getLong(sizeIndex)
                        }
                    }
                } catch (_: Exception) {}
                if (fileSize < 0) {
                    try {
                        contentResolver.openAssetFileDescriptor(uri, "r")?.use { fileSize = it.length }
                    } catch (_: Exception) {}
                }
                val width = meta(MediaMetadataRetriever.METADATA_KEY_VIDEO_WIDTH)
                val height = meta(MediaMetadataRetriever.METADATA_KEY_VIDEO_HEIGHT)
                val durationMs = meta(MediaMetadataRetriever.METADATA_KEY_DURATION).toLongOrNull()
                val durationText = durationMs?.let {
                    val sec = it / 1000
                    "%02d:%02d:%02d".format(sec / 3600, (sec % 3600) / 60, sec % 60)
                } ?: "نامشخص"
                lines += "نام فایل: $fileName"
                lines += "ابعاد: $width × $height"
                lines += "فرمت ظرف: ${meta(MediaMetadataRetriever.METADATA_KEY_MIMETYPE)}"
                lines += "حجم: ${if (fileSize >= 0) "%.2f MB".format(fileSize / 1048576.0) else "نامشخص"}"
                lines += "مدت: $durationText"
                lines += "Bitrate: ${meta(MediaMetadataRetriever.METADATA_KEY_BITRATE)}"
                val tagKeys = listOf(
                    "عنوان" to MediaMetadataRetriever.METADATA_KEY_TITLE,
                    "هنرمند" to MediaMetadataRetriever.METADATA_KEY_ARTIST,
                    "آلبوم" to MediaMetadataRetriever.METADATA_KEY_ALBUM,
                    "تاریخ" to MediaMetadataRetriever.METADATA_KEY_DATE,
                    "سبک" to MediaMetadataRetriever.METADATA_KEY_GENRE,
                    "سازنده" to MediaMetadataRetriever.METADATA_KEY_AUTHOR,
                    "نویسنده" to MediaMetadataRetriever.METADATA_KEY_WRITER,
                    "آهنگساز" to MediaMetadataRetriever.METADATA_KEY_COMPOSER
                )
                lines += ""
                lines += "Tagهای موجود:"
                var hasTag = false
                for ((label, key) in tagKeys) {
                    val value = retriever?.extractMetadata(key)?.takeIf { it.isNotBlank() }
                    if (value != null) {
                        lines += "$label: $value"
                        hasTag = true
                    }
                }
                val appTag = getSharedPreferences("veft_video_tags", MODE_PRIVATE).getString("current_tag", "").orEmpty()
                if (appTag.isNotBlank()) {
                    lines += "Tag ثبت‌شده در VEFt: $appTag"
                    hasTag = true
                }
                if (!hasTag) lines += "Tag متنی ثبت‌شده‌ای پیدا نشد"
                extractor = MediaExtractor().apply { setDataSource(this@MainActivity, uri, null) }
                val audioTracks = mutableListOf<String>()
                val subtitleTracks = mutableListOf<String>()
                val videoTracks = mutableListOf<String>()
                for (i in 0 until extractor.trackCount) {
                    val format = extractor.getTrackFormat(i)
                    val mime = format.getString("mime") ?: "نوع ناشناخته"
                    val title = try { format.getString("title") } catch (_: Exception) { null }
                    val language = try { format.getString("language") } catch (_: Exception) { null }
                    val trackName = title?.takeIf { it.isNotBlank() } ?: language?.takeIf { it.isNotBlank() } ?: "بدون نام"
                    val details = buildString {
                        append("#${i + 1} $trackName — $mime")
                        if (format.containsKey(MediaFormat.KEY_CHANNEL_COUNT)) append("، کانال: ${format.getInteger(MediaFormat.KEY_CHANNEL_COUNT)}")
                        if (format.containsKey(MediaFormat.KEY_SAMPLE_RATE)) append("، نرخ نمونه: ${format.getInteger(MediaFormat.KEY_SAMPLE_RATE)} Hz")
                    }
                    when {
                        mime.startsWith("audio/") -> audioTracks += details
                        mime.startsWith("text/") || mime.contains("subtitle") || mime.contains("subpicture") -> subtitleTracks += details
                        mime.startsWith("video/") -> videoTracks += details
                    }
                }
                lines += ""
                lines += "کدک تصویر: ${videoTracks.joinToString(" | ").ifBlank { "نامشخص" }}"
                lines += "تعداد صدا: ${audioTracks.size}"
                lines += audioTracks.ifEmpty { listOf("ترک صوتی شناسایی نشد") }
                lines += "تعداد زیرنویس: ${subtitleTracks.size}"
                lines += subtitleTracks.ifEmpty { listOf("ترک زیرنویس شناسایی نشد") }
                lines += "تعداد ترک تصویر: ${videoTracks.size}"
            } catch (e: Exception) {
                lines += "خواندن کامل اطلاعات ناموفق بود: ${e.message ?: "خطای ناشناخته"}"
            } finally {
                try { extractor?.release() } catch (_: Exception) {}
                try { retriever?.release() } catch (_: Exception) {}
            }
            runOnUiThread {
                statusText.text = "اطلاعات ویدیو آماده شد"
                AlertDialog.Builder(this)
                    .setTitle("Video Info")
                    .setMessage(lines.joinToString("\n"))
                    .setPositiveButton("بستن", null)
                    .show()
            }
        }
    }

    /** Keep the actual video, crop handles, and placement overlay aligned to the source frame. */
    private var sourceVideoWidth: Int = 16
    private var sourceVideoHeight: Int = 9

    private fun updatePlayerViewport(videoWidth: Int, videoHeight: Int) {
        if (videoWidth <= 0 || videoHeight <= 0) return
        sourceVideoWidth = videoWidth
        sourceVideoHeight = videoHeight
        val container = findViewById<FrameLayout>(R.id.playerContainer)
        val parent = container.parent as? View
        val availableWidth = ((parent?.width ?: container.width) -
            (parent?.paddingLeft ?: container.paddingLeft) -
            (parent?.paddingRight ?: container.paddingRight)).coerceAtLeast(1)
        // Use the full height of the player row instead of the old fixed 160dp cap.
        // This enlarges the real video viewport (not merely the surrounding black row)
        // while preserving the source aspect ratio and never stretching the picture.
        val maxHeight = (parent?.height ?: dp(160)).coerceAtLeast(1)
        val aspect = videoWidth.toFloat() / videoHeight.toFloat()
        var viewportWidth = availableWidth
        var viewportHeight = (viewportWidth / aspect).toInt().coerceAtLeast(1)
        if (viewportHeight > maxHeight) {
            viewportHeight = maxHeight
            viewportWidth = (viewportHeight * aspect).toInt().coerceAtLeast(1)
        }
        val containerParams = container.layoutParams
        containerParams.width = viewportWidth
        containerParams.height = viewportHeight
        if (containerParams is LinearLayout.LayoutParams) {
            // Center the actual video frame vertically in the resizable player row.
            containerParams.gravity = Gravity.CENTER
        }
        container.layoutParams = containerParams

        // All player layers share one exact viewport so crop/placement controls
        // remain aligned and keep their original touch/visual behavior.
        videoView.layoutParams = FrameLayout.LayoutParams(viewportWidth, viewportHeight, Gravity.CENTER)
        cropOverlay.layoutParams = FrameLayout.LayoutParams(viewportWidth, viewportHeight, Gravity.CENTER)
        placementOverlay.layoutParams = FrameLayout.LayoutParams(viewportWidth, viewportHeight, Gravity.CENTER)
        overlayVideoLayer.layoutParams = FrameLayout.LayoutParams(viewportWidth, viewportHeight, Gravity.CENTER)
        findViewById<ImageView>(R.id.playerColorPreview).layoutParams =
            FrameLayout.LayoutParams(viewportWidth, viewportHeight, Gravity.CENTER)
        container.requestLayout()
        container.post { updateOverlayPreviewLayout() }
    }

    /** Free Crop: drag the four corner handles directly over the player preview. */
    private fun toggleFreeCropMode() {
        if (selectedUri == null) {
            Toast.makeText(this, "ابتدا یک ویدیو انتخاب کنید", Toast.LENGTH_LONG).show()
            return
        }
        freeCropMode = !freeCropMode
        if (freeCropMode) {
            recordUndoState()
            cropOverlay.setMargins(cropLeftPct, cropTopPct, cropRightPct, cropBottomPct)
            cropOverlay.visibility = View.VISIBLE
            freeCropControls.visibility = View.VISIBLE
            cropSettingsSaved = false
            statusText.text = "Free Crop فعال است: چهار دستگیرهٔ گوشهٔ کادر را روی پلیر بکشید؛ سپس «ثبت محدوده» را بزنید و برای فایل نهایی از «خروجی تغییرات» استفاده کنید"
        } else {
            cropOverlay.visibility = View.GONE
            freeCropControls.visibility = View.GONE
            statusText.text = "حالت Free Crop بسته شد"
        }
    }

    private fun readCropOverlay() {
        val margins = cropOverlay.getMargins()
        cropLeftPct = margins[0]
        cropTopPct = margins[1]
        cropRightPct = margins[2]
        cropBottomPct = margins[3]
        if (autoCropMode) {
            // Add an approximately 2 mm safety margin around the manually framed subject.
            val extraX = ((dp(8).toFloat() / cropOverlay.width.coerceAtLeast(1)) * 100f).toInt().coerceAtLeast(1)
            val extraY = ((dp(8).toFloat() / cropOverlay.height.coerceAtLeast(1)) * 100f).toInt().coerceAtLeast(1)
            cropLeftPct = (cropLeftPct - extraX).coerceAtLeast(0)
            cropRightPct = (cropRightPct - extraX).coerceAtLeast(0)
            cropTopPct = (cropTopPct - extraY).coerceAtLeast(0)
            cropBottomPct = (cropBottomPct - extraY).coerceAtLeast(0)
        }
    }

    private fun validCropMargins(): Boolean {
        if (cropLeftPct + cropRightPct >= 90 || cropTopPct + cropBottomPct >= 90) {
            Toast.makeText(this, "باید بخشی از تصویر در هر دو جهت باقی بماند", Toast.LENGTH_LONG).show()
            return false
        }
        return true
    }

    private inner class FreeCropOverlayView : View(this@MainActivity) {
        private val borderPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.rgb(67, 217, 163); style = Paint.Style.STROKE; strokeWidth = 3f }
        private val shadePaint = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = 0x99000000.toInt(); style = Paint.Style.FILL }
        private val handlePaint = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.rgb(255, 210, 31); style = Paint.Style.FILL }
        private val labelPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.WHITE; textSize = 12f; textAlign = Paint.Align.CENTER }
        private var left = 0.08f
        private var top = 0.08f
        private var right = 0.92f
        private var bottom = 0.92f
        private var activeCorner = -1
        private var draggingFrame = false
        private var dragStartX = 0f
        private var dragStartY = 0f
        private var dragStartLeft = 0f
        private var dragStartTop = 0f
        private var dragStartRight = 0f
        private var dragStartBottom = 0f
        private val handleRadius get() = 16f * resources.displayMetrics.density

        init { visibility = View.GONE; isClickable = true }

        fun setMargins(l: Int, t: Int, r: Int, b: Int) {
            left = (l / 100f).coerceIn(0f, 0.44f)
            top = (t / 100f).coerceIn(0f, 0.44f)
            right = (1f - r / 100f).coerceIn(0.56f, 1f)
            bottom = (1f - b / 100f).coerceIn(0.56f, 1f)
            if (right - left < 0.12f) { left = 0.08f; right = 0.92f }
            if (bottom - top < 0.12f) { top = 0.08f; bottom = 0.92f }
            invalidate()
        }

        fun getMargins(): List<Int> = listOf(
            (left * 100).toInt().coerceIn(0, 44),
            (top * 100).toInt().coerceIn(0, 44),
            ((1f - right) * 100).toInt().coerceIn(0, 44),
            ((1f - bottom) * 100).toInt().coerceIn(0, 44)
        )

        override fun onDraw(canvas: Canvas) {
            super.onDraw(canvas)
            if (width <= 0 || height <= 0) return
            val l = left * width; val t = top * height; val r = right * width; val b = bottom * height
            canvas.drawRect(0f, 0f, width.toFloat(), t, shadePaint)
            canvas.drawRect(0f, b, width.toFloat(), height.toFloat(), shadePaint)
            canvas.drawRect(0f, t, l, b, shadePaint)
            canvas.drawRect(r, t, width.toFloat(), b, shadePaint)
            canvas.drawRect(l, t, r, b, borderPaint)
            val points = arrayOf(l to t, r to t, l to b, r to b)
            points.forEach { (x, y) -> canvas.drawCircle(x, y, handleRadius, handlePaint); canvas.drawCircle(x, y, handleRadius * 0.48f, borderPaint) }
            canvas.drawText("گوشه‌ها را بکشید", width / 2f, (t + b) / 2f, labelPaint)
        }

        override fun onTouchEvent(event: MotionEvent): Boolean {
            val x = event.x.coerceIn(0f, width.toFloat()); val y = event.y.coerceIn(0f, height.toFloat())
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    // Lock the outer ScrollView for the complete crop gesture.
                    parent?.requestDisallowInterceptTouchEvent(true)
                    val corners = arrayOf(left * width to top * height, right * width to top * height, left * width to bottom * height, right * width to bottom * height)
                    activeCorner = corners.indices.minByOrNull { i ->
                        val dx = corners[i].first - x; val dy = corners[i].second - y; dx * dx + dy * dy
                    } ?: -1
                    val nearest = corners.getOrNull(activeCorner)
                    if (nearest == null || kotlin.math.hypot((nearest.first - x).toDouble(), (nearest.second - y).toDouble()) > handleRadius * 2.5) activeCorner = -1
                    // Touching inside the crop frame moves the whole frame; touching a corner resizes it.
                    draggingFrame = activeCorner == -1 && x in (left * width)..(right * width) && y in (top * height)..(bottom * height)
                    dragStartX = x; dragStartY = y
                    dragStartLeft = left; dragStartTop = top; dragStartRight = right; dragStartBottom = bottom
                    return true
                }
                MotionEvent.ACTION_MOVE -> {
                    val minX = 0.08f; val minY = 0.08f
                    if (draggingFrame) {
                        val dx = (x - dragStartX) / width.coerceAtLeast(1)
                        val dy = (y - dragStartY) / height.coerceAtLeast(1)
                        val frameW = dragStartRight - dragStartLeft
                        val frameH = dragStartBottom - dragStartTop
                        left = (dragStartLeft + dx).coerceIn(0f, 1f - frameW)
                        top = (dragStartTop + dy).coerceIn(0f, 1f - frameH)
                        right = left + frameW
                        bottom = top + frameH
                        invalidate(); return true
                    }
                    when (activeCorner) {
                        0 -> { left = (x / width).coerceIn(0f, right - minX); top = (y / height).coerceIn(0f, bottom - minY) }
                        1 -> { right = (x / width).coerceIn(left + minX, 1f); top = (y / height).coerceIn(0f, bottom - minY) }
                        2 -> { left = (x / width).coerceIn(0f, right - minX); bottom = (y / height).coerceIn(top + minY, 1f) }
                        3 -> { right = (x / width).coerceIn(left + minX, 1f); bottom = (y / height).coerceIn(top + minY, 1f) }
                    }
                    invalidate(); return true
                }
                MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                    activeCorner = -1
                    draggingFrame = false
                    parent?.requestDisallowInterceptTouchEvent(false)
                    performClick()
                    return true
                }
            }
            return true
        }

        override fun performClick(): Boolean { super.performClick(); return true }
    }

    /** Unified final export combining configured crop, color, text, overlay video, audio and subtitle. */
    private fun exportCombinedChanges() {
        val sourceUri = selectedUri
        if (sourceUri == null) {
            Toast.makeText(this, "ابتدا ویدیوی اصلی را انتخاب کنید", Toast.LENGTH_LONG).show()
            return
        }
        if (freeCropMode) {
            readCropOverlay()
            if (!validCropMargins()) return
            cropSettingsSaved = true
            freeCropMode = false
            cropOverlay.visibility = View.GONE
            freeCropControls.visibility = View.GONE
        }
        val text = findViewById<EditText>(R.id.overlayTextInput).text.toString().trim()
        val secondUri = overlayVideoUri
        val audioUri = externalAudioUri
        val subtitleUri = externalSubtitleUri
        val textStartMs = if (text.isNotEmpty()) parseTimeInput(findViewById<EditText>(R.id.overlayTextStartTime).text.toString()) else 0L
        val textEndMs = if (text.isNotEmpty()) parseTimeInput(findViewById<EditText>(R.id.overlayTextEndTime).text.toString()) else videoDurationMs
        if (text.isNotEmpty() && (textStartMs == null || textEndMs == null || textEndMs <= textStartMs)) {
            Toast.makeText(this, "زمان شروع و پایان متن را درست وارد کنید", Toast.LENGTH_LONG).show(); return
        }
        val overlayStartMs = if (secondUri != null) parseTimeInput(findViewById<EditText>(R.id.overlayVideoStartTime).text.toString()) else 0L
        val overlayEndMs = if (secondUri != null) parseTimeInput(findViewById<EditText>(R.id.overlayVideoEndTime).text.toString()) else videoDurationMs
        if (secondUri != null && (overlayStartMs == null || overlayEndMs == null || overlayEndMs <= overlayStartMs || overlayStartMs >= videoDurationMs || overlayEndMs > videoDurationMs)) {
            Toast.makeText(this, "زمان شروع و پایان نمایش ویدیوی رویی را درست وارد کنید", Toast.LENGTH_LONG).show(); return
        }
        if (cropSettingsSaved && !validCropMargins()) return
        val chosenCoverFrame = selectedCoverFrameIndex
        if (chosenCoverFrame != null && frameBitmaps[chosenCoverFrame] == null) {
            Toast.makeText(this, "تصویر فریم انتخابی هنوز آماده نیست؛ یک بار دیگر اسلاید را انتخاب کنید", Toast.LENGTH_LONG).show()
            return
        }
        if (chosenCoverFrame != null && outputContainerMatroska) {
            Toast.makeText(this, "کاور انتخابی در خروجی MP4 پشتیبانی می‌شود؛ فرمت خروجی را به MP4 تغییر دهید", Toast.LENGTH_LONG).show()
            return
        }

        // Keep legacy timeline/storyboard-only workflows reachable from the single visible output button.
        val rgbNow = currentRgbProfile()
        val globalColorChanged = rgbNow != RgbProfile(1f, 1f, 1f, 1f)
        val coverSelected = selectedCoverFrameIndex != null
        val hasCombinedEdits = (cropSettingsSaved && (cropLeftPct > 0 || cropTopPct > 0 || cropRightPct > 0 || cropBottomPct > 0)) ||
            text.isNotEmpty() || secondUri != null || audioUri != null || subtitleUri != null || globalColorChanged || autoColorEnabled || coverSelected
        val hasTimelineEdits = selectedTimelineRange != null || timelineSplitPoints.isNotEmpty() || deletedTimelineRanges.isNotEmpty()
        val hasStoryboardEdits = selectedFrames.isNotEmpty() || deletedStoryboardFrames.isNotEmpty()
        val otherVisualEdits = (cropSettingsSaved && (cropLeftPct > 0 || cropTopPct > 0 || cropRightPct > 0 || cropBottomPct > 0)) ||
            text.isNotEmpty() || secondUri != null || globalColorChanged || autoColorEnabled || coverSelected
        if (trackClips.isNotEmpty() && !otherVisualEdits && !hasTimelineEdits && !hasStoryboardEdits && frameColorProfiles.isEmpty()) {
            exportTrackTimeline()
            return
        }
        if (trackClips.isNotEmpty() && otherVisualEdits) {
            Toast.makeText(this, "جایگاه و برش ترک‌های نوار در خروجی مستقل اعمال می‌شود؛ برای حفظ زمان‌بندی ترک‌ها ابتدا خروجی ترک‌ها را بگیرید یا ویرایش تصویری را جداگانه صادر کنید.", Toast.LENGTH_LONG).show()
            return
        }
        if (hasTimelineEdits && !hasCombinedEdits) {
            when {
                selectedTimelineRange != null -> exportOnlyTimelineRange(selectedTimelineRange!!)
                else -> exportTimelineEditedVideo()
            }
            return
        }
        if (hasStoryboardEdits && !hasCombinedEdits && !hasTimelineEdits) {
            if (selectedFrames.isNotEmpty()) exportSelectedStoryboardFramesSeparately()
            else exportRemainingVideo(false)
            return
        }
        if (frameColorProfiles.isNotEmpty() && !hasCombinedEdits && !hasTimelineEdits && !hasStoryboardEdits) {
            exportColorizedVideo()
            return
        }
        if (hasTimelineEdits && hasCombinedEdits) {
            Toast.makeText(this, "برش‌های نوار زمان هنوز با افکت‌های تصویری/صدا در یک فیلتر واحد ترکیب نشده‌اند؛ ابتدا برش‌های نوار زمان را بازنشانی کنید یا فقط خروجی برش را بگیرید.", Toast.LENGTH_LONG).show()
            return
        }
        if (hasStoryboardEdits && hasCombinedEdits) {
            Toast.makeText(this, "انتخاب‌های خروجی استوری‌بورد با افکت‌های سراسری هنوز در یک خروجی ترکیب نمی‌شوند؛ ابتدا انتخاب استوری‌بورد را لغو کنید.", Toast.LENGTH_LONG).show()
            return
        }

        val cropChanged = cropSettingsSaved && (cropLeftPct > 0 || cropTopPct > 0 || cropRightPct > 0 || cropBottomPct > 0)
        // Keep this decision outside the try block so the completion callback can report it.
        val requiresVideoReencode = cropChanged || text.isNotEmpty() || secondUri != null || globalColorChanged || autoColorEnabled
        val button = findViewById<Button>(R.id.outputChangesButton)
        button.isEnabled = false
        statusText.text = "در حال ترکیب تغییرات تصویری و ترک‌های پشتیبانی‌شده در یک خروجی…"
        worker.execute {
            var baseFile: File? = null
            var overlayFile: File? = null
            var audioFile: File? = null
            var subtitleFile: File? = null
            var textFile: File? = null
            var coverFile: File? = null
            var coverWasAdded = false
            var output: File? = null
            var error: String? = null
            try {
                baseFile = copyUriToCache(sourceUri, "evc_combined_base")
                if (secondUri != null) overlayFile = copyUriToCache(secondUri, "evc_combined_overlay")
                if (audioUri != null) audioFile = copyUriToCache(audioUri, "evc_combined_audio")
                if (subtitleUri != null) subtitleFile = copyUriToCache(subtitleUri, "evc_combined_subtitle")
                if (text.isNotEmpty()) {
                    textFile = File(cacheDir, "evc_combined_text_${System.currentTimeMillis()}.txt")
                    textFile.writeText(text, Charsets.UTF_8)
                }
                val coverIndex = selectedCoverFrameIndex
                val coverBitmap = coverIndex?.let { frameBitmaps[it] }
                var coverInputIndex: Int? = null
                if (coverBitmap != null && !outputContainerMatroska) {
                    coverFile = File(cacheDir, "evc_cover_${System.currentTimeMillis()}.jpg")
                    FileOutputStream(coverFile).use { coverBitmap.compress(Bitmap.CompressFormat.JPEG, 92, it) }
                }
                val ext = outputExtension()
                output = File(cacheDir, "evc_changes_${System.currentTimeMillis()}.$ext")
                val args = mutableListOf("-y", "-filter_threads", "1", "-filter_complex_threads", "1", "-threads", "1", "-i", baseFile.absolutePath)
                var nextInput = 1
                val overlayIndex = if (overlayFile != null) nextInput++ else null
                if (overlayFile != null) args.addAll(listOf("-stream_loop", "-1", "-i", overlayFile.absolutePath))
                val audioIndex = if (audioFile != null) nextInput++ else null
                if (audioFile != null) args.addAll(listOf("-i", audioFile.absolutePath))
                val subtitleIndex = if (subtitleFile != null) nextInput++ else null
                if (subtitleFile != null) args.addAll(listOf("-i", subtitleFile.absolutePath))
                if (coverFile != null) {
                    coverInputIndex = nextInput++
                    args.addAll(listOf("-i", coverFile.absolutePath))
                }

                // Audio/subtitle-only exports must not touch the video bitstream. Use FFmpeg
                // stream copy unless a real visual edit requires filtering/re-encoding.
                val graph = mutableListOf<String>()
                var current = "0:v"
                if (requiresVideoReencode && cropChanged) {
                    val widthPct = (100 - cropLeftPct - cropRightPct).coerceIn(10, 100)
                    val heightPct = (100 - cropTopPct - cropBottomPct).coerceIn(10, 100)
                    graph.add("[$current]crop=iw*$widthPct/100:ih*$heightPct/100:iw*$cropLeftPct/100:ih*$cropTopPct/100[evc_crop]")
                    current = "evc_crop"
                }
                if (requiresVideoReencode && autoColorEnabled) {
                    // Heuristic colorization: bright pixels lean sky-blue, darker midtones green,
                    // and middle/high midtones warm. This is not semantic AI object recognition.
                    graph.add("[$current]format=gray,split=7[evc_sky_src][evc_green_src][evc_skin_src][evc_sky_luma][evc_green_luma][evc_skin_luma][evc_gray_final]")
                    graph.add("[evc_sky_src]colorize=hue=210:saturation=0.32:mix=0.62,format=yuv420p[evc_sky]")
                    graph.add("[evc_green_src]colorize=hue=105:saturation=0.28:mix=0.48,format=yuv420p[evc_green]")
                    graph.add("[evc_skin_src]colorize=hue=25:saturation=0.24:mix=0.34,format=yuv420p[evc_skin]")
                    graph.add("[evc_sky_luma]lut=y='if(gte(val,175),255,0)'[evc_sky_mask]")
                    graph.add("[evc_green_luma]lut=y='if(between(val,35,145),255,0)'[evc_green_mask]")
                    graph.add("[evc_skin_luma]lut=y='if(between(val,90,205),255,0)'[evc_skin_mask]")
                    graph.add("[evc_gray_final]format=yuv420p[evc_gray_colorbase]")
                    graph.add("[evc_gray_colorbase][evc_sky][evc_sky_mask]maskedmerge[evc_auto_sky]")
                    graph.add("[evc_auto_sky][evc_green][evc_green_mask]maskedmerge[evc_auto_green]")
                    graph.add("[evc_auto_green][evc_skin][evc_skin_mask]maskedmerge[evc_auto]")
                    current = "evc_auto"
                }
                val rgb = currentRgbProfile()
                if (requiresVideoReencode) {
                    graph.add("[$current]colorchannelmixer=rr=${rgb.red}:gg=${rgb.green}:bb=${rgb.blue},eq=saturation=${rgb.saturation}[evc_color]")
                    current = "evc_color"
                }
                if (requiresVideoReencode && overlayIndex != null) {
                    val w = overlayVideoWidthPercent.coerceIn(5, 90)
                    val x = overlayVideoXPercent.coerceIn(0, 100 - w)
                    val y = overlayVideoYPercent.coerceIn(0, 95)
                    graph.add("[$overlayIndex:v][$current]scale2ref=w=main_w*$w/100:h=ow/mdar[evc_small][evc_base]")
                    val overlayStartSeconds = String.format(java.util.Locale.US, "%.3f", (overlayStartMs ?: 0L) / 1000.0)
                    val overlayEndSeconds = String.format(java.util.Locale.US, "%.3f", (overlayEndMs ?: videoDurationMs) / 1000.0)
                    graph.add("[evc_base][evc_small]overlay=x='main_w*$x/100':y='main_h*$y/100':eof_action=pass:enable='between(t\\,$overlayStartSeconds\\,$overlayEndSeconds)'[evc_overlay]")
                    current = "evc_overlay"
                }
                if (requiresVideoReencode && textFile != null) {
                    val safePath = textFile.absolutePath.replace("\\", "\\\\").replace(":", "\\:").replace("'", "\\'")
                    val startSeconds = String.format(java.util.Locale.US, "%.3f", (textStartMs ?: 0L) / 1000.0)
                    val endSeconds = String.format(java.util.Locale.US, "%.3f", (textEndMs ?: videoDurationMs) / 1000.0)
                    val draw = "drawtext=fontfile='/system/fonts/Roboto-Regular.ttf':textfile='$safePath':fontsize=${liveTextSize.coerceIn(8,160)}:fontcolor=white:borderw=2:bordercolor=black:x='w*${textXPercent.coerceIn(0,100)}/100':y='h*${textYPercent.coerceIn(0,100)}/100':enable='between(t\\,$startSeconds\\,$endSeconds)'"
                    graph.add("[$current]$draw[evc_text]")
                    current = "evc_text"
                }
                if (requiresVideoReencode) {
                    args.addAll(listOf("-filter_complex", graph.joinToString(";"), "-map", "[$current]"))
                    args.addAll(listOf("-c:v", "libx264", "-preset", "ultrafast", "-tune", "fastdecode", "-threads", "1", "-crf", "20", "-pix_fmt", "yuv420p"))
                } else {
                    // No visual changes: retain the exact original video codec/bitstream.
                    args.addAll(listOf("-map", "0:v:0", "-c:v", "copy"))
                }
                if (audioIndex != null) {
                    // Only the selected audio is encoded if needed; the video remains stream-copied.
                    args.addAll(listOf("-map", "$audioIndex:a:0", "-af", "apad", "-c:a", "aac", "-b:a", "192k", "-shortest"))
                } else if (requiresVideoReencode) {
                    // Keep the legacy compatible audio encode only when the image is being rendered.
                    args.addAll(listOf("-map", "0:a?", "-c:a", "aac", "-b:a", "192k"))
                } else {
                    // Audio/subtitle-only export also preserves the source audio bitstream.
                    args.addAll(listOf("-map", "0:a?", "-c:a", "copy"))
                }
                if (subtitleIndex != null) {
                    args.addAll(listOf("-map", "$subtitleIndex:s:0"))
                    args.addAll(listOf("-c:s", if (outputContainerMatroska) "copy" else "mov_text"))
                }
                // MP4 cover art is stored as a separate attached-picture stream, not burned into the video.
                if (coverInputIndex != null) {
                    args.addAll(listOf("-map", "$coverInputIndex:v:0", "-c:v:1", "mjpeg", "-disposition:v:1", "attached_pic"))
                    coverWasAdded = true
                }
                if (!outputContainerMatroska) args.addAll(listOf("-movflags", "+faststart"))
                args.addAll(listOf("-max_muxing_queue_size", "1024", "-f", if (outputContainerMatroska) "matroska" else "mp4", output.absolutePath))
                val session = FFmpegKit.executeWithArguments(args.toTypedArray())
                if (!ReturnCode.isSuccess(session.returnCode) || !output.exists() || output.length() == 0L) {
                    throw IllegalStateException("ساخت خروجی تغییرات ناموفق بود: ${session.allLogsAsString.takeLast(1600)}")
                }
            } catch (e: Exception) {
                error = e.message ?: e.javaClass.simpleName
                output?.delete(); output = null
            } finally {
                baseFile?.delete(); overlayFile?.delete(); audioFile?.delete(); subtitleFile?.delete(); textFile?.delete(); coverFile?.delete()
            }
            mainHandler.post {
                button.isEnabled = true
                val result = output
                if (result == null || !result.exists() || result.length() == 0L) {
                    statusText.text = "خروجی تغییرات ناموفق بود: ${error ?: "خطای ناشناخته"}"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                    result?.delete()
                    return@post
                }
                try {
                    val finalExt = outputExtension()
                    val values = ContentValues().apply {
                        put(MediaStore.Video.Media.DISPLAY_NAME, requestedOutputDisplayName("EVC_Changes_${System.currentTimeMillis()}", finalExt))
                        put(MediaStore.Video.Media.MIME_TYPE, outputMimeType())
                        if (android.os.Build.VERSION.SDK_INT >= 29) {
                            put(MediaStore.Video.Media.RELATIVE_PATH, Environment.DIRECTORY_MOVIES + "/EVC")
                            put(MediaStore.Video.Media.IS_PENDING, 1)
                        }
                    }
                    val outUri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
                        ?: throw IllegalStateException("ساخت فایل در Movies/EVC ممکن نشد")
                    contentResolver.openOutputStream(outUri)?.use { stream -> FileInputStream(result).use { it.copyTo(stream) } }
                        ?: throw IllegalStateException("نوشتن فایل خروجی ناموفق بود")
                    if (android.os.Build.VERSION.SDK_INT >= 29) contentResolver.update(outUri, ContentValues().apply { put(MediaStore.Video.Media.IS_PENDING, 0) }, null, null)
                    result.delete()
                    val applied = mutableListOf<String>()
                    if (cropSettingsSaved && (cropLeftPct > 0 || cropTopPct > 0 || cropRightPct > 0 || cropBottomPct > 0)) applied.add("Crop")
                    applied.add("رنگ")
                    if (text.isNotEmpty()) applied.add("متن")
                    if (secondUri != null) applied.add("ویدیوی رویی")
                    if (audioUri != null) applied.add("صدای جایگزین")
                    if (subtitleUri != null) applied.add("زیرنویس")
                    if (coverWasAdded) applied.add("کاور انتخابی")
                    restoreNormalStoryboardAfterExport()
                    statusText.text = if (!requiresVideoReencode) {
                        "خروجی (${applied.joinToString("، ")}) در Movies/EVC ذخیره شد؛ کدک ویدیوی اصلی بدون رمزگذاری مجدد حفظ شد."
                    } else {
                        "خروجی مشترک (${applied.joinToString("، ")}) در Movies/EVC ذخیره شد؛ برای اعمال تغییرات تصویری، ویدیو دوباره رمزگذاری شد."
                    }
                    Toast.makeText(this, "خروجی تغییرات در Movies/EVC ذخیره شد", Toast.LENGTH_LONG).show()
                } catch (e: Exception) {
                    result.delete()
                    statusText.text = "ذخیرهٔ خروجی تغییرات ناموفق بود: ${e.message ?: "خطا"}"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                }
            }
        }
    }

    private fun exportCroppedVideo() {
        val source = selectedUri
        if (source == null) {
            Toast.makeText(this, "ابتدا یک ویدیو انتخاب کنید", Toast.LENGTH_LONG).show()
            return
        }
        if (!cropSettingsSaved) {
            Toast.makeText(this, "ابتدا تنظیمات Crop را ثبت کنید", Toast.LENGTH_LONG).show()
            return
        }
        val output = File(cacheDir, "evc_crop_${System.currentTimeMillis()}.mp4")
        val button = findViewById<Button>(R.id.cropButton)
        button.isEnabled = false
        statusText.text = "در حال اعمال Crop واقعی و رمزگذاری مجدد ویدیو…"
        try {
            val left = (-1f + 2f * cropLeftPct / 100f).coerceIn(-1f, 0.98f)
            val right = (1f - 2f * cropRightPct / 100f).coerceIn(-0.98f, 1f)
            val top = (1f - 2f * cropTopPct / 100f).coerceIn(-0.98f, 1f)
            val bottom = (-1f + 2f * cropBottomPct / 100f).coerceIn(-1f, 0.98f)
            val cropEffect = Crop(left, right, bottom, top)
            val item = EditedMediaItem.Builder(MediaItem.fromUri(source))
                .setEffects(Effects(emptyList(), listOf(cropEffect)))
                .build()
            val composition = Composition.Builder(EditedMediaItemSequence.Builder(item).build()).build()
            val transformer = Transformer.Builder(this)
                .addListener(object : Transformer.Listener {
                    override fun onCompleted(composition: Composition, exportResult: ExportResult) {
                        activeTransformer = null
                        try {
                            val values = ContentValues().apply {
                                put(MediaStore.Video.Media.DISPLAY_NAME, requestedOutputDisplayName("EVC_Crop_${System.currentTimeMillis()}", "mp4"))
                                put(MediaStore.Video.Media.MIME_TYPE, "video/mp4")
                                if (android.os.Build.VERSION.SDK_INT >= 29) {
                                    put(MediaStore.Video.Media.RELATIVE_PATH, Environment.DIRECTORY_MOVIES + "/EVC")
                                    put(MediaStore.Video.Media.IS_PENDING, 1)
                                }
                            }
                            val outUri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
                                ?: throw IllegalStateException("ساخت فایل در Movies/EVC ممکن نشد")
                            contentResolver.openOutputStream(outUri)?.use { out -> FileInputStream(output).use { it.copyTo(out) } }
                                ?: throw IllegalStateException("نوشتن فایل Crop ناموفق بود")
                            if (android.os.Build.VERSION.SDK_INT >= 29) contentResolver.update(outUri, ContentValues().apply {
                                put(MediaStore.Video.Media.IS_PENDING, 0)
                            }, null, null)
                            writeOutputInfoReport(outUri)
                            output.delete()
                            button.isEnabled = true
                    restoreNormalStoryboardAfterExport()
                            statusText.text = "خروجی Crop واقعی در Movies/EVC ذخیره شد. برای اعمال برش، ویدیو رمزگذاری مجدد شده است."
                            Toast.makeText(this@MainActivity, statusText.text, Toast.LENGTH_LONG).show()
                        } catch (e: Exception) {
                            output.delete(); button.isEnabled = true
                            statusText.text = "ذخیرهٔ Crop ناموفق بود: ${e.message ?: "خطا"}"
                            Toast.makeText(this@MainActivity, statusText.text, Toast.LENGTH_LONG).show()
                        }
                    }
                    override fun onError(composition: Composition, exportResult: ExportResult, exportException: ExportException) {
                        activeTransformer = null; output.delete(); button.isEnabled = true
                        statusText.text = "خروجی Crop ناموفق بود: ${exportException.message ?: "خطای رمزگذاری"}"
                        Toast.makeText(this@MainActivity, statusText.text, Toast.LENGTH_LONG).show()
                    }
                }).build()
            activeTransformer = transformer
            transformer.start(composition, output.absolutePath)
        } catch (e: Exception) {
            activeTransformer = null; output.delete(); button.isEnabled = true
            statusText.text = "شروع خروجی Crop ناموفق بود: ${e.message ?: "خطا"}"
            Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
        }
    }

    private fun exportRemainingVideo(onlySelected: Boolean = false) {
        // Storyboard selection has explicit priority when its mode is active. Do this
        // BEFORE checking the timeline range: a stale timeline selection must never
        // redirect a storyboard export into the whole-video/timeline export path.
        if (onlySelected) {
            selectedTimelineRange = null
            exportSelectedStoryboardFramesSeparately()
            return
        }
        // A range explicitly selected on the timeline belongs to the timeline section.
        // Export only that range; never mix it with storyboard deletions or other ranges.
        val timelineRange = selectedTimelineRange
        if (timelineRange != null) {
            exportOnlyTimelineRange(timelineRange)
            return
        }
        val source = selectedUri
        if (source == null || videoDurationMs <= 0L) {
            Toast.makeText(this, "ابتدا یک ویدیوی معتبر انتخاب کنید", Toast.LENGTH_SHORT).show()
            return
        }
        val total = activeStoryboardFrameCount
        val requestedFrames = selectedFrames.toSet()
        if (onlySelected && requestedFrames.isEmpty()) {
            Toast.makeText(this, "برای این حالت، ابتدا اسلایدهایی را که باید در خروجی باشند انتخاب کنید", Toast.LENGTH_LONG).show()
            return
        }
        val kept = if (onlySelected) requestedFrames.filter { it !in deletedStoryboardFrames } else (0 until total).filter { it !in deletedStoryboardFrames }
        if (kept.isEmpty()) {
            Toast.makeText(this, if (onlySelected) "هیچ اسلاید انتخاب‌شدهٔ قابل‌خروجی وجود ندارد" else "همهٔ بازه‌ها حذف شده‌اند؛ چیزی برای خروجی باقی نمانده است", Toast.LENGTH_LONG).show()
            return
        }
        // Current version exports the remaining intervals without re-encoding.
        // The target-size/re-encoding mode will be added separately to avoid silently
        // changing codec or quality in the original-quality mode.
        statusText.text = if (onlySelected) "در حال ساخت خروجی بدون تغییر کدک از اسلایدهای انتخاب‌شده…" else "در حال ساخت خروجی بدون تغییر کدک از بازه‌های باقی‌مانده…"
        findViewById<Button>(R.id.outputChangesButton).isEnabled = false
        worker.execute {
            var result: File? = null
            var error: String? = null
            try {
                val excluded = mutableListOf<Pair<Long, Long>>()
                var runStart: Int? = null
                for (i in 0 until total) {
                    val shouldExclude = if (onlySelected) i !in requestedFrames || i in deletedStoryboardFrames else i in deletedStoryboardFrames
                    if (shouldExclude && runStart == null) runStart = i
                    if ((!shouldExclude || i == total - 1) && runStart != null) {
                        val endIndex = if (shouldExclude && i == total - 1) i + 1 else i
                        val startMs = videoDurationMs * runStart!! / total
                        val endMs = videoDurationMs * endIndex / total
                        if (endMs > startMs) excluded.add(startMs to endMs)
                        runStart = null
                    }
                }
                // Storyboard export is isolated: do not import deletions from the timeline section.
                val mergedExcluded = excluded.sortedBy { it.first }.fold(mutableListOf<Pair<Long, Long>>()) { acc, r ->
                    if (acc.isNotEmpty() && r.first <= acc.last().second) {
                        val last = acc.removeAt(acc.lastIndex); acc.add(last.first to max(last.second, r.second))
                    } else acc.add(r)
                    acc
                }
                val keptRanges = mutableListOf<Pair<Long, Long>>()
                var cursor = 0L
                for (r in mergedExcluded) {
                    val a = r.first.coerceIn(0L, videoDurationMs); val b = r.second.coerceIn(0L, videoDurationMs)
                    if (a > cursor) keptRanges.add(cursor to a)
                    cursor = max(cursor, b)
                }
                if (cursor < videoDurationMs) keptRanges.add(cursor to videoDurationMs)
                result = muxRemainingRanges(source, keptRanges)
            } catch (e: Exception) {
                error = e.message ?: e.javaClass.simpleName
            }
            mainHandler.post {
                findViewById<Button>(R.id.outputChangesButton).isEnabled = true
                val file = result
                if (file != null && file.exists() && file.length() > 0L) {
                    try {
                        val values = ContentValues().apply {
                            put(MediaStore.Video.Media.DISPLAY_NAME, requestedOutputDisplayName("EVC_edited_${System.currentTimeMillis()}", outputExtension()))
                            put(MediaStore.Video.Media.MIME_TYPE, outputMimeType())
                            if (android.os.Build.VERSION.SDK_INT >= 29) {
                                put(MediaStore.Video.Media.RELATIVE_PATH, Environment.DIRECTORY_MOVIES + "/EVC")
                                put(MediaStore.Video.Media.IS_PENDING, 1)
                            }
                        }
                        val outUri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
                        if (outUri == null) throw IllegalStateException("ساخت فایل در پوشهٔ Movies/EVC ممکن نشد")
                        contentResolver.openOutputStream(outUri)?.use { out -> FileInputStream(file).use { input -> input.copyTo(out) } }
                            ?: throw IllegalStateException("نوشتن فایل خروجی ناموفق بود")
                        if (android.os.Build.VERSION.SDK_INT >= 29) {
                            val done = ContentValues().apply { put(MediaStore.Video.Media.IS_PENDING, 0) }
                            contentResolver.update(outUri, done, null, null)
                        }
                        writeOutputInfoReport(outUri)
                        file.delete()
                    restoreNormalStoryboardAfterExport()
                        statusText.text = "ویدیوی خروجی در Movies/EVC ذخیره شد (بدون رمزگذاری مجدد)"
                        Toast.makeText(this, "ویدیوی خروجی در پوشهٔ Movies/EVC ذخیره شد", Toast.LENGTH_LONG).show()
                    } catch (e: Exception) {
                        statusText.text = "انتقال خروجی به پوشهٔ ویدیوها ناموفق بود: ${e.message ?: "خطا"}"
                        Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                    }
                } else {
                    statusText.text = "ساخت ویدیوی خروجی ناموفق بود: ${error ?: "فرمت یا برش پشتیبانی نشد"}"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                }
            }
        }
    }



    private fun exportOnlyTimelineRange(range: Pair<Long, Long>) {
        val source = selectedUri
        if (source == null || videoDurationMs <= 0L) {
            Toast.makeText(this, "ابتدا یک ویدیوی معتبر انتخاب کنید", Toast.LENGTH_SHORT).show(); return
        }
        val start = range.first.coerceIn(0L, videoDurationMs)
        val end = range.second.coerceIn(0L, videoDurationMs)
        if (end <= start) { Toast.makeText(this, "بازهٔ انتخاب‌شده معتبر نیست", Toast.LENGTH_SHORT).show(); return }
        val button = findViewById<Button>(R.id.outputChangesButton)
        button.isEnabled = false
        statusText.text = "در حال خروجی گرفتن فقط از ${formatTime(start)} تا ${formatTime(end)}…"
        worker.execute {
            var result: File? = null
            var error: String? = null
            try { result = muxRemainingRanges(source, listOf(start to end)) }
            catch (e: Exception) { error = e.message ?: e.javaClass.simpleName }
            mainHandler.post {
                button.isEnabled = true
                val file = result
                if (file == null || !file.exists() || file.length() == 0L) {
                    statusText.text = "خروجی بازهٔ نوار زمان ناموفق بود: ${error ?: "خطای ناشناخته"}"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show(); return@post
                }
                try {
                    val values = ContentValues().apply {
                        put(MediaStore.Video.Media.DISPLAY_NAME, requestedOutputDisplayName("EVC_timeline_${System.currentTimeMillis()}", outputExtension()))
                        put(MediaStore.Video.Media.MIME_TYPE, outputMimeType())
                        if (android.os.Build.VERSION.SDK_INT >= 29) {
                            put(MediaStore.Video.Media.RELATIVE_PATH, Environment.DIRECTORY_MOVIES + "/EVC")
                            put(MediaStore.Video.Media.IS_PENDING, 1)
                        }
                    }
                    val outUri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
                        ?: throw IllegalStateException("ساخت فایل خروجی ممکن نشد")
                    contentResolver.openOutputStream(outUri)?.use { out -> FileInputStream(file).use { input -> input.copyTo(out) } }
                        ?: throw IllegalStateException("نوشتن فایل خروجی ناموفق بود")
                    if (android.os.Build.VERSION.SDK_INT >= 29) contentResolver.update(outUri, ContentValues().apply { put(MediaStore.Video.Media.IS_PENDING, 0) }, null, null)
                    writeOutputInfoReport(outUri)
                    file.delete()
                    selectedTimelineRange = null
                    restoreNormalStoryboardAfterExport()
                    statusText.text = "فقط بازهٔ انتخاب‌شده در Movies/EVC ذخیره شد؛ تنظیمات استوری‌بورد و حذف‌ها دخالت داده نشدند"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                } catch (e: Exception) {
                    statusText.text = "ذخیرهٔ فایل ناموفق بود: ${e.message ?: "خطا"}"
                    Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
                }
            }
        }
    }

    /** Exports ONLY the selected storyboard time intervals, concatenated in selection order.
     *  The intervals are built from the storyboard's active start/end range, not the full video.
     *  No complement/remaining-video ranges are ever added to this export.
     */
    private fun exportSelectedStoryboardFramesSeparately() {
        val source = selectedUri
        if (source == null || videoDurationMs <= 0L) {
            Toast.makeText(this, "ابتدا یک ویدیوی معتبر انتخاب کنید", Toast.LENGTH_SHORT).show()
            return
        }
        val total = activeStoryboardFrameCount
        val chosen = selectedFrames.toSet()
            .filter { it in 0 until total && it !in deletedStoryboardFrames }
            .sorted()
        if (chosen.isEmpty()) {
            statusText.text = "خروجی انجام نشد: هیچ اسلایدی برای خروجی انتخاب نشده است"
            Toast.makeText(this, "خروجی لغو شد؛ ابتدا اسلایدهای موردنظر را انتخاب کنید", Toast.LENGTH_LONG).show()
            return
        }

        val rangeStart = storyboardStartMs.coerceIn(0L, videoDurationMs)
        val rangeEnd = (if (storyboardEndMs > rangeStart) storyboardEndMs else videoDurationMs)
            .coerceIn(rangeStart, videoDurationMs)
        if (rangeEnd <= rangeStart) {
            Toast.makeText(this, "بازهٔ زمانی استوری‌بورد معتبر نیست", Toast.LENGTH_LONG).show()
            return
        }

        // Build output intervals ONLY from selected storyboard indices. Consecutive
        // selected cells are joined into one range; any unselected cell closes the range.
        // Do not compute the complement (all unselected/remaining intervals).
        val selectedRanges = mutableListOf<Pair<Long, Long>>()
        var runStartIndex: Int? = null
        var previousIndex: Int? = null
        fun appendSelectedRun(firstIndex: Int, lastIndex: Int) {
            val a = storyboardTimestampForIndex(firstIndex, total, rangeStart, rangeEnd)
                .coerceIn(rangeStart, rangeEnd)
            // Use the next cell boundary as the end, even when a custom interval is set.
            // This keeps the selected run from spilling into the next unselected cell.
            val b = storyboardTimestampForIndex(lastIndex + 1, total, rangeStart, rangeEnd)
                .coerceIn(rangeStart, rangeEnd)
            if (b > a) selectedRanges.add(a to b)
        }
        for (index in chosen) {
            if (runStartIndex == null) {
                runStartIndex = index
                previousIndex = index
            } else if (previousIndex != null && index == previousIndex!! + 1) {
                previousIndex = index
            } else {
                appendSelectedRun(runStartIndex!!, previousIndex!!)
                runStartIndex = index
                previousIndex = index
            }
        }
        if (runStartIndex != null && previousIndex != null) {
            appendSelectedRun(runStartIndex!!, previousIndex!!)
        }
        // Keep the ranges as constructed from selected runs. Do not merge across gaps:
        // a gap represents at least one unselected storyboard cell and must stay excluded.
        val normalizedSelectedRanges = selectedRanges.toList()
        if (selectedRanges.isEmpty()) {
            Toast.makeText(this, "بازهٔ زمانی معتبری در اسلایدهای انتخاب‌شده وجود ندارد", Toast.LENGTH_LONG).show()
            return
        }

        val button = findViewById<Button>(R.id.outputChangesButton)
        button.isEnabled = false
        statusText.text = "در حال ساخت خروجی فقط از ${normalizedSelectedRanges.size} بازهٔ پیوستهٔ انتخاب‌شده؛ اسلایدهای انتخاب‌نشده وارد خروجی نمی‌شوند…"
        worker.execute {
            var temp: File? = null
            var outUri: Uri? = null
            var error: String? = null
            try {
                temp = muxRemainingRanges(source, normalizedSelectedRanges)
                val values = ContentValues().apply {
                    put(MediaStore.Video.Media.DISPLAY_NAME, requestedOutputDisplayName("EVC_selected_storyboard_${System.currentTimeMillis()}", outputExtension()))
                    put(MediaStore.Video.Media.MIME_TYPE, outputMimeType())
                    if (android.os.Build.VERSION.SDK_INT >= 29) {
                        put(MediaStore.Video.Media.RELATIVE_PATH, Environment.DIRECTORY_MOVIES + "/EVC")
                        put(MediaStore.Video.Media.IS_PENDING, 1)
                    }
                }
                outUri = contentResolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values)
                    ?: throw IllegalStateException("ساخت فایل خروجی ناموفق بود")
                contentResolver.openOutputStream(outUri)?.use { output ->
                    FileInputStream(temp).use { input -> input.copyTo(output) }
                } ?: throw IllegalStateException("نوشتن فایل خروجی ناموفق بود")
                if (android.os.Build.VERSION.SDK_INT >= 29) {
                    contentResolver.update(outUri, ContentValues().apply {
                        put(MediaStore.Video.Media.IS_PENDING, 0)
                    }, null, null)
                }
                writeOutputInfoReport(outUri!!)
            } catch (e: Exception) {
                error = e.message ?: e.javaClass.simpleName
                outUri?.let { try { contentResolver.delete(it, null, null) } catch (_: Exception) { } }
            } finally {
                temp?.delete()
            }
            mainHandler.post {
                button.isEnabled = true
                if (error == null && outUri != null) {
                    restoreNormalStoryboardAfterExport()
                    statusText.text = "فقط ${normalizedSelectedRanges.size} بازهٔ پیوستهٔ انتخاب‌شده در یک فایل ذخیره شد؛ بازه‌های انتخاب‌نشده وارد خروجی نشدند"
                } else {
                    statusText.text = "خروجی اسلایدهای انتخاب‌شده ناموفق بود: ${error ?: "خطای ناشناخته"}"
                }
                Toast.makeText(this, statusText.text, Toast.LENGTH_LONG).show()
            }
        }
    }

    /**
     * Default output name follows the first source video's filename and adds today's date.
     * For Merge/Join, the first item in the ordered input list is the naming source.
     * The manual-name checkbox remains an explicit override.
     */
    private fun requestedOutputDisplayName(defaultBase: String, extension: String): String {
        val raw = if (manualOutputNameEnabled) {
            findViewById<EditText>(R.id.manualOutputName).text.toString().trim()
        } else {
            val firstInput = mergeUris.firstOrNull() ?: selectedUri
            val sourceName = firstInput?.let { uri ->
                try { displayNameForUri(uri) } catch (_: Exception) { null }
            }.orEmpty()
            val sourceBase = sourceName.substringBeforeLast('.', sourceName).ifBlank { defaultBase }
            val date = java.text.SimpleDateFormat("yyyy-MM-dd", java.util.Locale.getDefault())
                .format(java.util.Date())
            "${sourceBase}_$date"
        }
        val clean = raw.substringBeforeLast('.', raw)
            .replace(Regex("""[\\/:*?"<>|]"""), "_")
            .trim().take(100)
        return "${clean.ifBlank { defaultBase }}.$extension"
    }

    private fun outputExtension(): String = if (outputContainerMatroska) "mkv" else "mp4"
    private fun outputMimeType(): String = if (outputContainerMatroska) "video/x-matroska" else "video/mp4"

    /**
     * Builds an MKV output using FFmpeg stream-copy only: no audio/video re-encoding.
     * The source URI is copied to cache first so document-provider URIs work too.
     * Stream-copy cuts are keyframe-dependent and may not land on the exact requested frame.
     */
    private fun muxRangesToMatroska(source: Uri, ranges: List<Pair<Long, Long>>): File {
        val stamp = System.currentTimeMillis()
        val input = File(cacheDir, "evc_mkv_source_$stamp.bin")
        val segments = mutableListOf<File>()
        val concatList = File(cacheDir, "evc_mkv_concat_$stamp.txt")
        val output = File(cacheDir, "evc_export_$stamp.mkv")
        try {
            contentResolver.openInputStream(source)?.use { src ->
                input.outputStream().use { dst -> src.copyTo(dst) }
            } ?: throw IllegalStateException("خواندن فایل ویدیوی اصلی ممکن نشد")
            if (input.length() == 0L) throw IllegalStateException("فایل ویدیوی اصلی خالی است")

            ranges.filter { it.second > it.first }.forEachIndexed { index, range ->
                val segment = File(cacheDir, "evc_mkv_part_${stamp}_$index.mkv")
                val start = range.first.coerceAtLeast(0L) / 1000.0
                val duration = (range.second - range.first).coerceAtLeast(0L) / 1000.0
                if (duration <= 0.0) return@forEachIndexed
                val args = arrayOf(
                    "-y", "-ss", String.format(java.util.Locale.US, "%.3f", start),
                    "-i", input.absolutePath, "-t", String.format(java.util.Locale.US, "%.3f", duration),
                    "-map", "0", "-c", "copy", "-avoid_negative_ts", "make_zero",
                    "-f", "matroska", segment.absolutePath
                )
                val session = FFmpegKit.executeWithArguments(args)
                if (!ReturnCode.isSuccess(session.returnCode) || !segment.exists() || segment.length() == 0L) {
                    throw IllegalStateException("ساخت قطعهٔ MKV ناموفق بود: ${session.allLogsAsString.takeLast(900)}")
                }
                segments.add(segment)
            }
            if (segments.isEmpty()) throw IllegalStateException("هیچ بازهٔ معتبری برای خروجی MKV وجود ندارد")
            concatList.writeText(segments.joinToString("\n") { segment ->
                "file '${segment.absolutePath.replace("'", "'\\''")}'"
            } + "\n")
            val concatArgs = arrayOf(
                "-y", "-f", "concat", "-safe", "0", "-i", concatList.absolutePath,
                "-map", "0", "-c", "copy", "-f", "matroska", output.absolutePath
            )
            val concatSession = FFmpegKit.executeWithArguments(concatArgs)
            if (!ReturnCode.isSuccess(concatSession.returnCode) || !output.exists() || output.length() == 0L) {
                throw IllegalStateException("ادغام قطعات MKV ناموفق بود: ${concatSession.allLogsAsString.takeLast(900)}")
            }
            return output
        } catch (e: Exception) {
            output.delete()
            throw e
        } finally {
            input.delete()
            concatList.delete()
            segments.forEach { it.delete() }
        }
    }

    private fun muxRemainingRanges(source: Uri, ranges: List<Pair<Long, Long>>): File {
        if (outputContainerMatroska) return muxRangesToMatroska(source, ranges)
        val probe = MediaExtractor()
        probe.setDataSource(this, source, null)
        val videoTrack = (0 until probe.trackCount).firstOrNull {
            probe.getTrackFormat(it).getString(MediaFormat.KEY_MIME)?.startsWith("video/") == true
        } ?: run { probe.release(); throw IllegalStateException("ترک ویدیویی پیدا نشد") }
        // Android's MPEG-4 MediaMuxer only supports a subset of MP4 tracks. Never silently
        // discard subtitles, timed metadata, or other non-A/V tracks during a modified export.
        val unsupportedTracks = mutableListOf<String>()
        for (i in 0 until probe.trackCount) {
            val format = probe.getTrackFormat(i)
            val mime = format.getString(MediaFormat.KEY_MIME) ?: "unknown/unknown"
            if (!mime.startsWith("video/") && !mime.startsWith("audio/")) unsupportedTracks.add("#$i $mime")
        }
        if (unsupportedTracks.isNotEmpty()) {
            probe.release()
            throw IllegalStateException(
                "این ویدیو ترک‌های غیرصوتی/تصویری دارد (${unsupportedTracks.joinToString()})؛ " +
                "خروجی‌گیر فعلی اندروید قادر به حفظ مطمئن زیرنویس/داده‌های آن نیست. برای جلوگیری از حذف بی‌صدا، خروجی لغو شد. " +
                "برای حفظ همهٔ ترک‌ها باید خروجی‌گیر FFmpeg با پشتیبانی از کپی همهٔ ترک‌ها اضافه شود."
            )
        }
        val output = File(cacheDir, "evc_export_${System.currentTimeMillis()}.mp4")
        val muxer = MediaMuxer(output.absolutePath, MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4)
        val trackMap = mutableMapOf<Int, Int>()
        for (i in 0 until probe.trackCount) {
            val format = probe.getTrackFormat(i)
            val mime = format.getString(MediaFormat.KEY_MIME) ?: continue
            if (mime.startsWith("video/") || mime.startsWith("audio/")) {
                try {
                    trackMap[i] = muxer.addTrack(format)
                    probe.selectTrack(i)
                } catch (e: Exception) {
                    try { muxer.release() } catch (_: Exception) { }
                    probe.release()
                    throw IllegalStateException("حفظ ترک $i با کدک $mime توسط خروجی‌گیر MP4 اندروید پشتیبانی نشد؛ برای جلوگیری از حذف ترک، خروجی لغو شد.", e)
                }
            }
        }
        if (trackMap.isEmpty()) { probe.release(); muxer.release(); throw IllegalStateException("ترک قابل خروجی پیدا نشد") }
        muxer.start()
        val buffer = java.nio.ByteBuffer.allocate(8 * 1024 * 1024)
        val info = MediaCodec.BufferInfo()
        var outputBaseUs = 0L
        try {
            for ((requestedStartMs, requestedEndMs) in ranges) {
                if (requestedEndMs <= requestedStartMs) continue
                val syncProbe = MediaExtractor()
                syncProbe.setDataSource(this, source, null)
                syncProbe.selectTrack(videoTrack)
                syncProbe.seekTo(requestedStartMs * 1000L, MediaExtractor.SEEK_TO_PREVIOUS_SYNC)
                var actualStartUs = if (syncProbe.sampleTrackIndex == videoTrack) syncProbe.sampleTime else -1L
                if (actualStartUs < 0L) {
                    syncProbe.seekTo(requestedStartMs * 1000L, MediaExtractor.SEEK_TO_NEXT_SYNC)
                    actualStartUs = if (syncProbe.sampleTrackIndex == videoTrack) syncProbe.sampleTime else -1L
                }
                syncProbe.release()
                if (actualStartUs < 0L || actualStartUs >= requestedEndMs * 1000L) continue

                // First lightweight pass finds the first video PTS for timestamp normalization.
                val startProbe = MediaExtractor()
                startProbe.setDataSource(this, source, null)
                startProbe.selectTrack(videoTrack)
                startProbe.seekTo(actualStartUs, MediaExtractor.SEEK_TO_PREVIOUS_SYNC)
                val segmentStartUs = if (startProbe.sampleTrackIndex == videoTrack) startProbe.sampleTime else actualStartUs
                startProbe.release()

                // Start at the nearest preceding sync frame. Some phones/files have a
                // delayed or missing first keyframe; NEXT_SYNC can skip the whole selected
                // interval and produce an empty segment. PREVIOUS_SYNC keeps the segment
                // decodable; stream-copy boundaries remain keyframe-accurate, not frame-exact.
                probe.seekTo(actualStartUs, MediaExtractor.SEEK_TO_PREVIOUS_SYNC)
                while (probe.sampleTrackIndex >= 0) {
                    val track = probe.sampleTrackIndex
                    val pts = probe.sampleTime
                    if (pts >= requestedEndMs * 1000L) break
                    if (track in trackMap && pts >= actualStartUs) {
                        buffer.clear()
                        val size = probe.readSampleData(buffer, 0)
                        if (size > buffer.capacity()) throw IllegalStateException("نمونهٔ رسانه از ظرفیت بافر بیشتر است")
                        if (size > 0) {
                            info.set(0, size, outputBaseUs + (pts - segmentStartUs).coerceAtLeast(0L), probe.sampleFlags)
                            muxer.writeSampleData(trackMap.getValue(track), buffer, info)
                        }
                    }
                    if (!probe.advance()) break
                }
                outputBaseUs += (requestedEndMs * 1000L - segmentStartUs).coerceAtLeast(1L)
            }
        } finally {
            try { muxer.stop() } catch (_: Exception) { }
            muxer.release()
            probe.release()
        }
        if (!output.exists() || output.length() == 0L) {
            output.delete()
            throw IllegalStateException("هیچ بازهٔ قابل‌خروجی باقی نماند؛ ممکن است برش این کدک با حفظ کدک پشتیبانی نشود")
        }
        return output
    }

    private fun updateModeButtons() {
        timeModeButton.backgroundTintList = android.content.res.ColorStateList.valueOf(Color.rgb(255, 210, 31))
        timeModeButton.setTextColor(Color.rgb(7, 20, 47))
    }

    private fun updateStoryboardPlaybackHighlight(positionMs: Long) {
        if (frameViews.isEmpty() || videoDurationMs <= 0L) return
        val rangeStart = storyboardStartMs.coerceIn(0L, videoDurationMs)
        val rangeEnd = (if (storyboardEndMs > rangeStart) storyboardEndMs else videoDurationMs).coerceIn(rangeStart, videoDurationMs)
        val candidates = frameViews.keys.filter { it !in deletedStoryboardFrames }
        if (candidates.isEmpty()) return
        val current = candidates.minByOrNull { index -> kotlin.math.abs(storyboardTimestampForIndex(index, activeStoryboardFrameCount, rangeStart, rangeEnd) - positionMs) } ?: return
        val isPlaying = try { videoView.isPlaying } catch (_: Exception) { false }
        val blinkOn = isPlaying && (SystemClock.uptimeMillis() / 320L) % 2L == 0L
        if (playbackFrameIndex != current) {
            val previous = frameViews[playbackFrameIndex]
            previous?.alpha = 1f
            if (playbackFrameIndex >= 0) refreshCellStyle(playbackFrameIndex)
            playbackFrameIndex = current
        }
        frameViews.forEach { (index, cell) ->
            if (index == current) {
                cell.alpha = if (!isPlaying || blinkOn) 1f else 0.58f
                cell.foreground = playbackBorder(index in selectedFrames, blinkOn)
            } else {
                cell.alpha = 1f
                if (index == playbackFrameIndex || index in selectedFrames) refreshCellStyle(index)
            }
        }
        frameViews[current]?.postInvalidateOnAnimation()
    }

    private fun playbackBorder(selected: Boolean, bright: Boolean): android.graphics.drawable.Drawable = GradientDrawable().apply {
        setColor(Color.TRANSPARENT)
        cornerRadius = dp(2).toFloat()
        val color = if (bright) Color.rgb(255, 145, 35) else if (selected) Color.rgb(255, 190, 48) else Color.rgb(61, 91, 135)
        setStroke(dp(if (bright) 4 else if (selected) 3 else 1), color)
    }

    // Storyboard thumbnails were removed from the tool rail; keep this hook
    // so existing refresh call sites remain harmless.
    private fun refreshRailStoryboard() {
        // Intentionally empty.
    }

    private fun refreshSelectionStyles() {
        frameViews.keys.forEach { refreshCellStyle(it) }
    }
    private fun refreshCellStyle(index: Int) {
        val cell = frameViews[index] ?: return
        cell.foreground = makeBorder(index in selectedFrames)
        val badge = cell.tag as? TextView
        val isCover = selectedCoverFrameIndex == index
        badge?.text = if (isCover) "★" else "✓"
        badge?.setBackgroundColor(if (isCover) Color.rgb(65, 220, 180) else Color.rgb(255, 210, 31))
        badge?.visibility = if (isCover || index in selectedFrames) View.VISIBLE else View.GONE
    }
    /** Called by TimelineView when a yellow cut marker is dragged to a new timestamp. */
    fun onTimelineCutDragged(points: List<Long>) {
        timelineSplitPoints.clear()
        timelineSplitPoints.addAll(points)
        timelineView.setTimeline(videoDurationMs, timelineSplitPoints.toList(), deletedTimelineRanges)
        trackTimelineView.setClips(trackClips.toList(), videoDurationMs)
    }

    private fun updateSelectionText() {
        val coverLabel = selectedCoverFrameIndex?.let { " • کاور: فریم ${it + 1}" } ?: " • کاور: پیش‌فرض"
        selectionText.text = "اسلایدهای انتخاب‌شده: ${selectedFrames.size} • باقی‌مانده: ${frameViews.size} از $activeStoryboardFrameCount$coverLabel"
        refreshSelectionStyles()
    }
    private fun formatTime(ms: Long): String {
        val seconds = max(0L, ms / 1000L)
        val hours = seconds / 3600L
        val minutes = (seconds % 3600L) / 60L
        val secs = seconds % 60L
        return if (hours > 0L) String.format("%02d:%02d:%02d", hours, minutes, secs)
        else String.format("%02d:%02d", minutes, secs)
    }
    private fun dp(value: Int): Int = (value * resources.displayMetrics.density + 0.5f).toInt()

    override fun onPause() {
        mainHandler.removeCallbacks(playbackSyncRunnable)
        super.onPause()
        if (::videoView.isInitialized && videoView.isPlaying) videoView.pause()
    }
    override fun onResume() {
        super.onResume()
        if (::videoView.isInitialized && videoDurationMs > 0L) {
            mainHandler.removeCallbacks(playbackSyncRunnable)
            mainHandler.post(playbackSyncRunnable)
        }
    }
    override fun onDestroy() {
        storyboardGeneration++
        mainHandler.removeCallbacks(playbackSyncRunnable)
        mainHandler.removeCallbacks(storyboardAutoApplyRunnable)
        releaseOverlayPreviewPlayer()
        worker.shutdownNow()
        frameBitmaps.values.forEach { if (!it.isRecycled) it.recycle() }
        super.onDestroy()
    }
    companion object {
        private const val REQUEST_VIDEO = 2101
        private const val DEFAULT_STORYBOARD_FRAME_COUNT = 120
        private const val MAX_STORYBOARD_FRAME_COUNT = 5000
    }
}


/** Interactive timeline: one-finger drag scrubs; pinch changes the visible time scale. */
class TimelineView(context: android.content.Context, attrs: android.util.AttributeSet? = null) : View(context, attrs) {
    var onSeek: ((Long) -> Unit)? = null
    var onSelectRange: ((Pair<Long, Long>) -> Unit)? = null
    var playheadMs: Long = 0L
        private set
    private var durationMs = 0L
    private var splitPoints = listOf<Long>()
    private var deletedRanges = listOf<Pair<Long, Long>>()
    private var thumbnails: List<Pair<Long, Bitmap>> = emptyList()
    private var zoom = 1f
    private var windowStartMs = 0L
    private var lastX = 0f
    private var downX = 0f
    private var downY = 0f
    private var initialSpan = 0f
    private var initialZoom = 1f
    private var moved = false
    private var draggingPlayhead = false
    // A cut marker can be grabbed and moved independently from the playhead and timeline pan.
    private var draggingCutMs: Long? = null
    private val paint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val backgroundPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply { color = Color.rgb(8, 17, 32) }
    private val density = resources.displayMetrics.density

    fun setTimeline(duration: Long, cuts: List<Long>, deleted: List<Pair<Long, Long>>) {
        durationMs = duration.coerceAtLeast(0L)
        splitPoints = cuts.sorted()
        deletedRanges = deleted.toList()
        windowStartMs = windowStartMs.coerceIn(0L, max(0L, durationMs - visibleDuration()))
        invalidate()
    }
    fun setThumbnails(frames: List<Pair<Long, Bitmap>>) {
        val next = frames.filter { !it.second.isRecycled }.sortedBy { it.first }
        val retained = next.map { it.second }.toSet()
        thumbnails.map { it.second }.distinct().forEach { old ->
            if (old !in retained && !old.isRecycled) old.recycle()
        }
        thumbnails = next
        invalidate()
    }
    fun setPlayhead(timeMs: Long) {
        playheadMs = timeMs.coerceIn(0L, durationMs)
        // Auto-follow playback: let the playhead travel across the visible strip,
        // then move the timeline window when it approaches the right edge.
        if (durationMs > 0L) {
            val visible = visibleDuration()
            val end = windowStartMs + visible
            val followThreshold = windowStartMs + (visible * 0.82f).toLong()
            if (playheadMs > followThreshold && playheadMs < durationMs) {
                windowStartMs = (playheadMs - (visible * 0.72f).toLong())
                    .coerceIn(0L, max(0L, durationMs - visible))
            } else if (playheadMs < windowStartMs && playheadMs > 0L) {
                windowStartMs = (playheadMs - (visible * 0.15f).toLong())
                    .coerceIn(0L, max(0L, durationMs - visible))
            }
        }
        invalidate()
    }
    private fun visibleDuration(): Long = if (durationMs <= 0L) 1L else (durationMs / zoom).toLong().coerceAtLeast(1L)
    private fun timeAt(x: Float): Long {
        val usable = (width - 16f * density).coerceAtLeast(1f)
        return (windowStartMs + (((x - 8f * density).coerceIn(0f, usable) / usable) * visibleDuration().toFloat()).toLong()).coerceIn(0L, durationMs)
    }
    private fun xAt(time: Long): Float {
        val usable = (width - 16f * density).coerceAtLeast(1f)
        return 8f * density + ((time - windowStartMs).toFloat() / visibleDuration()).coerceIn(0f, 1f) * usable
    }
    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        val left = 8f * density; val right = width - left
        val top = height * .03f; val bottom = height * .97f
        paint.color = Color.rgb(37, 69, 111); canvas.drawRoundRect(left, top, right, bottom, 5f * density, 5f * density, paint)
        if (durationMs <= 0L) {
            paint.color = Color.LTGRAY; paint.textSize = 11f * density
            canvas.drawText("نوار زمان پس از انتخاب ویدیو آماده می‌شود", left, height * .58f, paint); return
        }
        val start = windowStartMs; val end = minOf(durationMs, start + visibleDuration())
        // Render extracted video frames as one continuous thumbnail strip across the timeline.
        if (thumbnails.isNotEmpty()) {
            val save = canvas.save()
            canvas.clipRect(left, top, right, bottom)
            // Preserve the complete source frame inside each time cell; no stretch or crop.
            thumbnails.forEachIndexed { index, frame ->
                val cellDuration = (durationMs.toFloat() / thumbnails.size.coerceAtLeast(1))
                val cellStart = frame.first
                val cellEnd = minOf(durationMs, (cellStart + cellDuration).toLong())
                val prevX = xAt(cellStart)
                val nextX = xAt(cellEnd)
                if (nextX < left || prevX > right) return@forEachIndexed
                val dst = RectF(max(left, prevX), top, minOf(right, nextX), bottom)
                if (dst.width() > 0f && dst.height() > 0f) {
                    val bitmap = frame.second
                    // Fill each timeline time-cell like a thumbnail preview; do not shrink
                    // the cell or leave letterbox gaps. Center-crop only the image to the cell.
                    val bitmapRatio = bitmap.width.toFloat() / bitmap.height.toFloat()
                    val targetRatio = dst.width() / dst.height()
                    val source = if (bitmapRatio > targetRatio) {
                        val cropWidth = (bitmap.height * targetRatio).toInt().coerceIn(1, bitmap.width)
                        val leftCrop = (bitmap.width - cropWidth) / 2
                        Rect(leftCrop, 0, leftCrop + cropWidth, bitmap.height)
                    } else {
                        val cropHeight = (bitmap.width / targetRatio).toInt().coerceIn(1, bitmap.height)
                        val topCrop = (bitmap.height - cropHeight) / 2
                        Rect(0, topCrop, bitmap.width, topCrop + cropHeight)
                    }
                    paint.color = Color.WHITE
                    canvas.drawBitmap(bitmap, source, dst, paint)
                }
            }
            canvas.restoreToCount(save)
            paint.color = Color.argb(18, 8, 17, 32)
            canvas.drawRoundRect(left, top, right, bottom, 5f * density, 5f * density, paint)
        }
        deletedRanges.forEach { r ->
            if (r.second >= start && r.first <= end) {
                paint.color = Color.rgb(181, 44, 69)
                canvas.drawRect(xAt(r.first), top, xAt(r.second), bottom, paint)
            }
        }
        splitPoints.filter { it in start..end }.forEach { cut ->
            paint.color = Color.rgb(255, 210, 31); paint.strokeWidth = 2f * density
            canvas.drawLine(xAt(cut), top - 5f * density, xAt(cut), bottom + 5f * density, paint)
        }
        paint.color = Color.WHITE; paint.textSize = 9f * density
        val px = xAt(playheadMs)
        paint.color = Color.argb(70, 30, 144, 255)
        canvas.drawRect(px - 7f * density, top, px + 7f * density, bottom, paint)
        paint.color = Color.rgb(40, 160, 255); paint.strokeWidth = 3.5f * density
        canvas.drawLine(px, top, px, bottom, paint)
        paint.style = Paint.Style.FILL
        canvas.drawCircle(px, top + 3f * density, 5f * density, paint)
        paint.color = Color.WHITE; paint.textSize = 9f * density
        val now = format(playheadMs)
        val nowX = (px + 5f * density).coerceAtMost(right - paint.measureText(now))
        canvas.drawText(now, nowX, 10f * density + 2f, paint)
        paint.color = Color.LTGRAY; paint.textSize = 8f * density
        canvas.drawText(format(start), left, height - 3f * density, paint)
        val endText = format(end); canvas.drawText(endText, right - paint.measureText(endText), height - 3f * density, paint)
    }
    override fun onTouchEvent(event: MotionEvent): Boolean {
        when (event.actionMasked) {
            MotionEvent.ACTION_DOWN -> {
                downX = event.x; lastX = event.x; downY = event.y; moved = false
                val markerX = xAt(playheadMs)
                draggingPlayhead = kotlin.math.abs(event.x - markerX) <= 20f * density
                // Yellow cut handles have priority over panning; touching one starts a cut drag.
                draggingCutMs = splitPoints.minByOrNull { kotlin.math.abs(xAt(it) - event.x) }
                    ?.takeIf { kotlin.math.abs(xAt(it) - event.x) <= 16f * density }
                if (draggingCutMs != null) draggingPlayhead = false
                parent?.requestDisallowInterceptTouchEvent(draggingCutMs != null || draggingPlayhead)
                return true
            }
            MotionEvent.ACTION_POINTER_DOWN -> if (event.pointerCount >= 2) { initialSpan = span(event); initialZoom = zoom; moved = true; return true }
            MotionEvent.ACTION_MOVE -> {
                if (event.pointerCount >= 2) {
                    val current = span(event)
                    if (initialSpan > 0f && current > 0f && durationMs > 0L) {
                        val focusTime = timeAt((event.getX(0) + event.getX(1)) / 2f)
                        zoom = (initialZoom * current / initialSpan).coerceIn(1f, 240f)
                        val focusX = ((event.getX(0) + event.getX(1)) / 2f)
                        val frac = ((focusX - 8f * density) / (width - 16f * density).coerceAtLeast(1f)).coerceIn(0f, 1f)
                        windowStartMs = (focusTime - (visibleDuration() * frac).toLong()).coerceIn(0L, max(0L, durationMs - visibleDuration()))
                        invalidate()
                    }
                    return true
                }
                val dx = event.x - lastX
                if (kotlin.math.abs(event.x - downX) > 5f * density) moved = true
                if (durationMs > 0L && moved) {
                    val cut = draggingCutMs
                    if (cut != null) {
                        val next = timeAt(event.x).coerceIn(250L, (durationMs - 250L).coerceAtLeast(250L))
                        splitPoints = (splitPoints - cut + next).distinct().sorted()
                        draggingCutMs = next
                        // Keep the main activity's authoritative split list in sync.
                        (context as? MainActivity)?.onTimelineCutDragged(splitPoints)
                    } else if (draggingPlayhead) {
                        playheadMs = timeAt(event.x)
                        onSeek?.invoke(playheadMs)
                    } else {
                        val usable = (width - 16f * density).coerceAtLeast(1f)
                        val shift = (-dx / usable * visibleDuration()).toLong()
                        windowStartMs = (windowStartMs + shift).coerceIn(0L, max(0L, durationMs - visibleDuration()))
                    }
                    invalidate()
                }
                lastX = event.x; return true
            }
            MotionEvent.ACTION_UP -> {
                if (!moved && durationMs > 0L && !draggingPlayhead && draggingCutMs == null) {
                    val t = timeAt(event.x)
                    // A tap is a seek operation: move the visible playhead and player
                    // to exactly the tapped timestamp, while retaining range selection.
                    playheadMs = t
                    onSeek?.invoke(t)
                    val boundaries = (listOf(0L) + splitPoints.filter { it in 0L..durationMs } + listOf(durationMs)).distinct().sorted()
                    val idx = (0 until boundaries.size - 1).firstOrNull { t >= boundaries[it] && t <= boundaries[it + 1] } ?: 0
                    if (boundaries.size > 1) onSelectRange?.invoke(boundaries[idx] to boundaries[idx + 1])
                    invalidate()
                }
                draggingPlayhead = false
                draggingCutMs = null
                parent?.requestDisallowInterceptTouchEvent(false)
                performClick(); return true
            }
            MotionEvent.ACTION_CANCEL -> { draggingPlayhead = false; draggingCutMs = null; parent?.requestDisallowInterceptTouchEvent(false); return true }
        }
        return true
    }
    override fun performClick(): Boolean { super.performClick(); return true }
    private fun span(e: MotionEvent): Float { if (e.pointerCount < 2) return 0f; val dx=e.getX(0)-e.getX(1); val dy=e.getY(0)-e.getY(1); return kotlin.math.sqrt(dx*dx+dy*dy) }
    private fun format(ms: Long): String { val s=(ms.coerceAtLeast(0L)/1000L); return String.format(java.util.Locale.US, "%02d:%02d", s/60, s%60) }
}


/** Two-lane timeline for externally added audio and subtitle clips. Drag a clip body to move it; drag either edge to trim. */
class TrackTimelineView(context: android.content.Context, attrs: android.util.AttributeSet? = null) : View(context, attrs) {
    var onClipSelected: ((TrackClip?) -> Unit)? = null
    var onClipsChanged: ((List<TrackClip>) -> Unit)? = null
    var selectedClipId: Long? = null
        private set
    val selectedClipIds: MutableSet<Long> = linkedSetOf()
    private var downAtMs = 0L
    private var longPressedSelection = false
    private var clips: List<TrackClip> = emptyList()
    private var videoDurationMs: Long = 0L
    private val p = Paint(Paint.ANTI_ALIAS_FLAG)
    private val d = resources.displayMetrics.density
    private var downX = 0f
    private var downY = 0f
    private var activeId: Long? = null
    private var mode = 0 // 0 move, 1 trim left, 2 trim right
    private var moved = false
    private var original: TrackClip? = null
    private var originalList: List<TrackClip> = emptyList()

    fun setClips(items: List<TrackClip>, duration: Long) {
        clips = items.toList(); videoDurationMs = duration.coerceAtLeast(1L)
        if (selectedClipId != null && clips.none { it.id == selectedClipId }) selectedClipId = null
        selectedClipIds.retainAll(clips.map { it.id }.toSet())
        invalidate()
    }
    fun selectClip(id: Long) { selectedClipId = id; selectedClipIds.clear(); selectedClipIds.add(id); onClipSelected?.invoke(clips.firstOrNull { it.id == id }); invalidate() }
    fun clearSelection() { selectedClipIds.clear(); selectedClipId = null; onClipSelected?.invoke(null); invalidate() }
    private fun xFor(ms: Long): Float = (ms.toDouble() / videoDurationMs.toDouble()).toFloat().coerceIn(0f, 1f) * width
    private fun timeFor(x: Float): Long = ((x / width.coerceAtLeast(1).toFloat()).coerceIn(0f, 1f) * videoDurationMs).toLong()
    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        val laneH = height / 3f
        p.textSize = 9f * d
        for (lane in 0..2) {
            val top = lane * laneH
            p.color = when (lane) {
                0 -> Color.rgb(17, 37, 59)
                1 -> Color.rgb(33, 27, 54)
                else -> Color.rgb(34, 48, 42)
            }
            canvas.drawRect(0f, top, width.toFloat(), top + laneH, p)
            p.color = Color.rgb(180, 202, 229)
            canvas.drawText(when (lane) { 0 -> "AUDIO"; 1 -> "SUBTITLE"; else -> "VIDEO" }, 4f * d, top + 10f * d, p)
        }
        if (videoDurationMs <= 1L) {
            p.color = Color.LTGRAY; canvas.drawText("پس از انتخاب ویدیو، ترک‌ها در اینجا نمایش داده می‌شوند", 8f * d, height / 2f, p); return
        }
        clips.forEach { clip ->
            val lane = when (clip.kind) { TrackClipKind.AUDIO -> 0; TrackClipKind.SUBTITLE -> 1; TrackClipKind.VIDEO -> 2 }
            val laneTop = lane * laneH
            val left = xFor(clip.startMs)
            val right = xFor(clip.startMs + clip.durationMs)
            val rect = RectF(left, laneTop + 14f * d, maxOf(left + 12f * d, right), laneTop + laneH - 3f * d)
            p.color = when {
                clip.id in selectedClipIds && clip.kind == TrackClipKind.AUDIO -> Color.rgb(255, 190, 48)
                clip.id in selectedClipIds && clip.kind == TrackClipKind.VIDEO -> Color.rgb(255, 160, 70)
                clip.id in selectedClipIds -> Color.rgb(218, 166, 255)
                clip.kind == TrackClipKind.AUDIO -> Color.rgb(64, 151, 229)
                clip.kind == TrackClipKind.VIDEO -> Color.rgb(70, 170, 120)
                else -> Color.rgb(153, 103, 204)
            }
            canvas.drawRoundRect(rect, 4f * d, 4f * d, p)
            p.color = Color.BLACK; p.textSize = 8f * d
            val label = clip.name.take(22) + "  ${clip.durationMs / 1000}s"
            canvas.save(); canvas.clipRect(rect); canvas.drawText(label, rect.left + 5f * d, rect.centerY() + 3f * d, p); canvas.restore()
            p.color = Color.WHITE
            canvas.drawRect(rect.left, rect.top, minOf(rect.right, rect.left + 4f * d), rect.bottom, p)
            canvas.drawRect(maxOf(rect.left, rect.right - 4f * d), rect.top, rect.right, rect.bottom, p)
        }
        val playhead = try { (context as? MainActivity)?.let { it.findViewById<TimelineView>(R.id.timelineView).playheadMs } ?: 0L } catch (_: Exception) { 0L }
        p.color = Color.WHITE; p.strokeWidth = 1.2f * d; canvas.drawLine(xFor(playhead), 0f, xFor(playhead), height.toFloat(), p)
    }
    override fun onTouchEvent(event: MotionEvent): Boolean {
        when (event.actionMasked) {
            MotionEvent.ACTION_DOWN -> {
                downX = event.x; downY = event.y; moved = false
                downAtMs = android.os.SystemClock.uptimeMillis(); longPressedSelection = false
                val lane = when {
                    event.y < height / 3f -> TrackClipKind.AUDIO
                    event.y < height * 2f / 3f -> TrackClipKind.SUBTITLE
                    else -> TrackClipKind.VIDEO
                }
                val hit = clips.asReversed().firstOrNull { clip ->
                    if (clip.kind != lane) false else {
                        val l = xFor(clip.startMs); val r = xFor(clip.startMs + clip.durationMs)
                        event.x >= l - 5f * d && event.x <= r + 5f * d
                    }
                }
                activeId = hit?.id; original = hit; originalList = clips.toList()
                if (hit != null) {
                    selectedClipId = hit.id
                    val left = xFor(hit.startMs); val right = xFor(hit.startMs + hit.durationMs)
                    mode = when { abs(event.x - left) <= 12f * d -> 1; abs(event.x - right) <= 12f * d -> 2; else -> 0 }
                    onClipSelected?.invoke(hit); invalidate()
                } else { selectedClipId = null; onClipSelected?.invoke(null); invalidate() }
                parent?.requestDisallowInterceptTouchEvent(true)
                return true
            }
            MotionEvent.ACTION_MOVE -> {
                val id = activeId ?: return true
                val clip = original ?: return true
                val delta = timeFor(event.x) - timeFor(downX)
                if (abs(event.x - downX) > 3f * d) moved = true
                if (!moved) return true
                val list = clips.toMutableList(); val i = list.indexOfFirst { it.id == id }; if (i < 0) return true
                val updated = when (mode) {
                    1 -> {
                        val newStart = (clip.startMs + delta).coerceIn(0L, clip.startMs + clip.durationMs - 500L)
                        val shift = newStart - clip.startMs
                        clip.copy(startMs = newStart, sourceStartMs = (clip.sourceStartMs + shift).coerceAtLeast(0L), durationMs = clip.durationMs - shift)
                    }
                    2 -> clip.copy(durationMs = (clip.durationMs + delta).coerceIn(500L, maxOf(500L, videoDurationMs - clip.startMs)))
                    else -> clip.copy(startMs = (clip.startMs + delta).coerceIn(0L, maxOf(0L, videoDurationMs - clip.durationMs)))
                }
                list[i] = updated; clips = list; invalidate(); onClipsChanged?.invoke(clips)
                return true
            }
            MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                if (!moved && activeId != null) {
                    val held = android.os.SystemClock.uptimeMillis() - downAtMs
                    if (event.actionMasked == MotionEvent.ACTION_UP && held >= android.view.ViewConfiguration.getLongPressTimeout()) {
                        activeId?.let { id ->
                            if (!selectedClipIds.add(id)) selectedClipIds.remove(id)
                            selectedClipId = selectedClipIds.lastOrNull()
                            longPressedSelection = true
                            onClipSelected?.invoke(clips.firstOrNull { it.id == selectedClipId })
                        }
                    } else if (!longPressedSelection) {
                        selectedClipIds.clear(); activeId?.let { selectedClipIds.add(it) }
                        onClipSelected?.invoke(clips.firstOrNull { it.id == activeId })
                    }
                    invalidate()
                }
                activeId = null; original = null; parent?.requestDisallowInterceptTouchEvent(false)
                performClick(); return true
            }
        }
        return true
    }
    override fun performClick(): Boolean { super.performClick(); return true }
}

/**
 * Scrolls the storyboard when the user drags anywhere on the table itself.
 * Vertical drags are intercepted after touch-slop; taps and horizontal gestures
 * remain available to storyboard cells and their selection controls.
 */
class StoryboardDragScrollView @JvmOverloads constructor(
    context: android.content.Context,
    attrs: android.util.AttributeSet? = null
) : ScrollView(context, attrs) {
    private val dragSlop = android.view.ViewConfiguration.get(context).scaledTouchSlop
    private var downX = 0f
    private var downY = 0f
    private var tableDragging = false

    override fun onInterceptTouchEvent(event: MotionEvent): Boolean {
        when (event.actionMasked) {
            MotionEvent.ACTION_DOWN -> {
                downX = event.x
                downY = event.y
                tableDragging = false
                // The inner storyboard owns this gesture; prevent the outer page
                // ScrollView from stealing a vertical drag that starts on a cell.
                parent?.requestDisallowInterceptTouchEvent(true)
            }
            MotionEvent.ACTION_MOVE -> {
                val dx = kotlin.math.abs(event.x - downX)
                val dy = kotlin.math.abs(event.y - downY)
                if (!tableDragging && dy > dragSlop && dy > dx * 1.10f) {
                    tableDragging = true
                    parent?.requestDisallowInterceptTouchEvent(true)
                    return true
                }
            }
            MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                if (!tableDragging) parent?.requestDisallowInterceptTouchEvent(false)
            }
        }
        return tableDragging || super.onInterceptTouchEvent(event)
    }

    override fun onTouchEvent(event: MotionEvent): Boolean {
        val handled = super.onTouchEvent(event)
        when (event.actionMasked) {
            MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                tableDragging = false
                parent?.requestDisallowInterceptTouchEvent(false)
            }
        }
        return handled
    }

    override fun performClick(): Boolean {
        super.performClick()
        return true
    }
}

/** A visible, draggable scrollbar thumb dedicated to the storyboard grid. */
class StoryboardScrollbarView @JvmOverloads constructor(
    context: android.content.Context,
    attrs: android.util.AttributeSet? = null
) : View(context, attrs) {
    private var targetScroll: ScrollView? = null
    private var content: View? = null
    private val density = resources.displayMetrics.density
    private val paint = Paint(Paint.ANTI_ALIAS_FLAG)
    private var dragging = false

    fun bind(scrollView: ScrollView, contentView: View) {
        targetScroll = scrollView
        content = contentView
        invalidate()
    }

    // The scrollbar rail is intentionally shorter than the storyboard viewport.
    override fun onMeasure(widthMeasureSpec: Int, heightMeasureSpec: Int) {
        val availableHeight = when (View.MeasureSpec.getMode(heightMeasureSpec)) {
            View.MeasureSpec.UNSPECIFIED -> (resources.displayMetrics.heightPixels * 0.50f).toInt()
            else -> View.MeasureSpec.getSize(heightMeasureSpec)
        }
        val railHeight = (availableHeight * 0.72f).toInt().coerceAtLeast((48f * density).toInt())
        val width = when (View.MeasureSpec.getMode(widthMeasureSpec)) {
            View.MeasureSpec.EXACTLY -> View.MeasureSpec.getSize(widthMeasureSpec)
            View.MeasureSpec.AT_MOST -> minOf((18f * density).toInt(), View.MeasureSpec.getSize(widthMeasureSpec))
            else -> (18f * density).toInt()
        }
        setMeasuredDimension(width, railHeight)
    }

    private fun maxScroll(): Int {
        val scroll = targetScroll ?: return 0
        val body = content ?: return 0
        return (body.height - scroll.height).coerceAtLeast(0)
    }

    private fun thumbHeight(): Float {
        val scroll = targetScroll ?: return height.toFloat()
        val body = content ?: return height.toFloat()
        if (height <= 0 || body.height <= 0) return height.toFloat()
        val visibleRatio = (scroll.height.toFloat() / body.height.toFloat()).coerceIn(0f, 1f)
        return max(36f * density, height * visibleRatio * 0.52f).coerceAtMost(height.toFloat())
    }

    private fun thumbTop(): Float {
        val range = maxScroll()
        val travel = (height - thumbHeight()).coerceAtLeast(0f)
        if (range <= 0 || travel <= 0f) return 0f
        return (targetScroll?.scrollY?.toFloat() ?: 0f) / range * travel
    }

    override fun onDraw(canvas: Canvas) {
        super.onDraw(canvas)
        val centerX = width / 2f
        paint.style = Paint.Style.FILL
        paint.color = Color.argb(95, 180, 205, 235)
        canvas.drawRoundRect(centerX - 1.1f * density, 0f, centerX + 1.1f * density, height.toFloat(), 3f * density, 3f * density, paint)
        val h = thumbHeight()
        val top = thumbTop()
        paint.color = if (dragging) Color.rgb(255, 235, 59) else Color.rgb(255, 193, 7)
        canvas.drawRoundRect(2f * density, top, width - 2f * density, top + h, 6f * density, 6f * density, paint)
        paint.color = Color.rgb(7, 20, 47)
        paint.strokeWidth = 1.2f * density
        val mid = width / 2f
        for (offset in -1..1) {
            canvas.drawLine(mid - 2.5f * density, top + h / 2f + offset * 3f * density,
                mid + 2.5f * density, top + h / 2f + offset * 3f * density, paint)
        }
    }

    private fun moveThumbTo(y: Float) {
        val scroll = targetScroll ?: return
        val range = maxScroll()
        val travel = (height - thumbHeight()).coerceAtLeast(0f)
        if (range <= 0 || travel <= 0f) return
        val top = (y - thumbHeight() / 2f).coerceIn(0f, travel)
        scroll.scrollTo(0, (top / travel * range).toInt())
        invalidate()
    }

    override fun onTouchEvent(event: MotionEvent): Boolean {
        when (event.actionMasked) {
            MotionEvent.ACTION_DOWN -> {
                dragging = true
                parent?.requestDisallowInterceptTouchEvent(true)
                moveThumbTo(event.y)
                invalidate()
                return true
            }
            MotionEvent.ACTION_MOVE -> {
                if (dragging) moveThumbTo(event.y)
                return true
            }
            MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                dragging = false
                parent?.requestDisallowInterceptTouchEvent(false)
                invalidate()
                performClick()
                return true
            }
        }
        return true
    }

    override fun performClick(): Boolean {
        super.performClick()
        return true
    }
}
