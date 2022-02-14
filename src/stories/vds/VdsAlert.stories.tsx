import { storiesOf } from '@storybook/react';
import { default as React } from 'react';
import { muiTheme } from 'storybook-addon-material-ui5';
import { version } from '../../../package.json';
import CodeHighlight from '../shared/CodeHighlight';
import { Highlight } from '../shared/Highlight';
import { BaseStoryLayout } from '../shared/StoryLayouts';
import { Alert_Error_Example, alert_error_example_snippet, Alert_Info_Example, alert_info_example_snippet, Alert_Success_Example, alert_success_example_snippet, Alert_Warning_Example, alert_warning_example_snippet } from '../snippets/VdsAlert.snippets';

const storyTitle = 'Alert';

storiesOf(`vds@${version}`, module)
  .addDecorator(muiTheme())
  .add(storyTitle, () => (
    <BaseStoryLayout storyTitle={storyTitle}>
      <p>Notifications are messages that communicate information to the user, they are purposefully non-interruptive.</p>
      <h3>Overview</h3>
      <p>
        Notifications keep user informed on system status and guarantee a better product experience.
        Since notifications are intrusive and may cause distraction, Vapor has 3 kind of notification (that differ from the interruptive modal dialogue that has a separate section) to differentiate their importance and the attention they grab from users.
        Keep in mind that notifications, unlike modals, are meant to let users continue their workflow therefore they do not require an additional overlay layer blocking the user from any further interaction until the notification gets dismissed.
      </p>
      <h3>Style</h3>
      <p>
        <b>Informative</b> are used to give user additional information, related or not to the action performed. They are normally timed and generally don't require any user action.
      </p>
      <CodeHighlight>
        <Alert_Info_Example />
      </CodeHighlight>
      <h3>Code</h3>
      <Highlight language='typescript'>{alert_info_example_snippet}</Highlight>
      <p>
        <b>Check</b> are used to show user confirmation and successful process. They are normally timed and generally don't require any user action.
      </p>
      <CodeHighlight>
        <Alert_Success_Example />
      </CodeHighlight>
      <h3>Code</h3>
      <Highlight language='typescript'>{alert_success_example_snippet}</Highlight>
      <p>
        <b>Warning</b> are used to report inconvenient results, or risky actions to user. They are also used to report system problem.  They are normally persistent and generally require user action to disappear.
      </p>
      <CodeHighlight>
        <Alert_Warning_Example />
      </CodeHighlight>
      <h3>Code</h3>
      <Highlight language='typescript'>{alert_warning_example_snippet}</Highlight>
      <p>
        <b>Error</b> are used for critical and blocking problems, both due to user action or systemic issues; they require user attention and need to be solved to proceed. They are persistent and require user action to disappear.   </p>
      <CodeHighlight>
        <Alert_Error_Example />
      </CodeHighlight>
      <h3>Code</h3>
      <Highlight language='typescript'>{alert_error_example_snippet}</Highlight>
    </BaseStoryLayout>
  ));
