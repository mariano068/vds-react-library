import { Cancel, EventNote } from '@mui/icons-material';
import { IconButton, styled } from '@mui/material';
import React from 'react';
import DatePicker, { ReactDatePickerProps } from 'react-datepicker';
import { VdsTextField } from '..';

const StyledDatepickerContainer: any = styled('div')(({ fullWidth }: any) => ({
    'display': 'flex',
    'fontFamily': '-apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Oxygen-Sans, Ubuntu, Cantarell, "Helvetica Neue", sans-serif',
    'flexDirection': 'column',
    'width': fullWidth ? 'initial' : '99%',
    'input': { padding: '0 !important' },
    'button': { padding: '0 !important' },
    minHeight: '96px',
    '.react-datepicker__input-container div': {
        minHeight: 'unset'
    }
}));

const StyledInfosContainer = styled('div')({
    'marginBottom': '12px',
    'display': 'flex',
    'flexDirection': 'column'
});

const StyledHelperTextContainer: any = styled('span')(({ disabled }: any) => ({
    'fontSize': "12px",
    'color': disabled ? '#C1C1C4' : "#9DA6AD",
    'lineHeight': "18px",
    'fontFamily': "Roboto",
    'fontWeight': 400,
    'textAlign': "left"
}));

const StyledLabelContainer = styled('span')(({ disabled, readOnly }: any) => ({
    'fontSize': "14px",
    'color': readOnly ? "black" : disabled ? "#9DA6AD" : "#152935",
    'letterSpacing': "0",
    'lineHeight': "18px",
    'fontFamily': "Roboto !important",
    'fontWeight': 500,
    'textAlign': "left",
    'marginBottom': '8px'
}));

export const VdsDatepicker = (props: ReactDatePickerProps & { error?: any, disabled?: any, fullWidth?: any, clear: any, errorText?: string, label: string, helperText?: string }) => {

    const {
        label,
        error,
        errorText,
        helperText,
        disabled,
        clear,
        ...DatepickerProps
    } = props;

    const FromDateInput = React.forwardRef(({ value, onClick }: any, ref: any) => {

        return (
            <VdsTextField
                ref={ref}
                size="small"
                value={value}
                error={error}
                errorText={errorText}
                disabled={disabled}
                endAdornment={(
                    <React.Fragment>
                        {!disabled && value && <IconButton style={{ padding: '0px !important' }} size="small" onClick={(ev) => {
                            ev.stopPropagation();
                            clear(null);
                        }}>
                            <Cancel style={{ fontSize: '16px', padding: '0px !important' }} />
                        </IconButton>}
                        <EventNote style={{ fontSize: '16px', padding: '0px !important' }} />
                    </React.Fragment>
                )}
                placeholder="---"
                fullWidth
                onClick={onClick}
            />
        )
    });

    return (
        <StyledDatepickerContainer fullWidth={props?.fullWidth}>
            {(label || helperText) && (
                <StyledInfosContainer>
                    {label && (
                        <StyledLabelContainer>
                            {label}
                        </StyledLabelContainer>
                    )}
                    {helperText && (
                        <StyledHelperTextContainer disabled={props?.disabled}>
                            {helperText}
                        </StyledHelperTextContainer>
                    )}
                </StyledInfosContainer>
            )}
            <DatePicker
                {...DatepickerProps}
                disabled={disabled}
                customInput={<FromDateInput/>}
            />
        </StyledDatepickerContainer>
    );
}
